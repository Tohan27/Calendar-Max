(function(){
  var now = new Date();
  var state = {
    year: now.getFullYear(),
    month: now.getMonth(),
    selYear: now.getFullYear(),
    selectedDates: new Set(),
    anchorDate: null,
    selectedMarkerId: null,
    expandedWeekIndex: null,
    stepSize: 30,
    pendingTime: null,
    selectedTimeMarkId: null,
    detailJustExpanded: false,
    expandMode: 'page',
    glass: false
  };

  var markers = [];
  var dateMarks = {};
  var timeMarks = {};
  var dateMarkValues = {};

  /* 多日历：calendars 保存所有日历（非当前日历的数据静默存放），
     markers/dateMarks/timeMarks/dateMarkValues/markerIdCounter 始终是「当前日历」的实时数据 */
  var calendars = [];
  var activeCalendarId = null;
  var renamingCalId = null;
  var calIdCounter = 0;

  /* 背景图片：整页展开 / 长页面展开各一套配置 */
  var backgrounds = {
    page: { imageId: null, opacity: 100, blur: 0 },
    long: { imageId: null, opacity: 100, blur: 0 }
  };
  var folderImageNames = [];   // image 文件夹里的图片文件名（相对 image/ 的路径）
  var localImages = [];        // 从前端导入的图片（存成 data URL）
  var hiddenImages = [];       // 被用户从列表里移除过的文件夹图片名（防止刷新时又被扫回来）
  var missingImages = {};      // 本次渲染中加载失败（文件不存在）的图片 id

  var valueEditor = { targets: [], active: 0 };
  var stepPresets = [10, 20, 30, 60];
  var optionPresets = {
    '2': [['真','假'],['正','负'],['对','错'],['好','坏'],['正','副']],
    '3': [['低','中','高'],['弱','中','强'],['小','中','大'],['坏','中','好']],
    '4': [['低','较低','较高','高'],['弱','较弱','较强','强'],['小','较小','较大','大'],['坏','较坏','较好','好']],
    '5': [['低','较低','中','较高','高'],['弱','较弱','中','较强','强'],['小','较小','中','较大','大'],['坏','较坏','中','较好','好']],
    '6': [],
    '7': []
  };
  var currentWeek = [];
  var markDrag = { active:false, mode:null, markId:null, dateKey:null, origStart:0, origEnd:0, curStart:0, curEnd:0, origColIdx:0, curColIdx:0, startX:0, startY:0, colH:576, colW:40, pressId:null, pressX:0, pressY:0, pressPending:false, pressTimer:null, progressTimer:null };
  var markerIdCounter = 0;
  var tempColor = '#3b82f6';
  var animating = false;

  var dateDrag = { active:false, anchor:null, additive:false, lastKey:null };
  var detailDrag = { active:false, col:null, anchor:null, shift:false };
  var dragTarget = { id:null, before:true };
  var editingMarkerId = null;

  var WD = ['一','二','三','四','五','六','日'];
  var WD_FULL = ['周一','周二','周三','周四','周五','周六','周日'];
  var HOUR_PX = 24;

  var PRESETS = [
    ['#ef4444','红色'], ['#f97316','橙色'], ['#eab308','黄色'], ['#22c55e','绿色'],
    ['#06b6d4','青色'], ['#3b82f6','蓝色'], ['#8b5cf6','紫色'], ['#ec4899','粉色'],
    ['#9ca3af','灰色'], ['#111827','黑色']
  ];

  function pad(n){ return (n<10?'0':'') + n; }
  function dateKey(y,m,d){ return y + '-' + pad(m+1) + '-' + pad(d); }
  function fmtDate(d){ return dateKey(d.getFullYear(), d.getMonth(), d.getDate()); }
  function daysInMonth(y,m){ return new Date(y, m+1, 0).getDate(); }
  function firstWeekday(y,m){ var d = new Date(y, m, 1).getDay(); return (d+6)%7; }
  function weekIndexFor(y,m,d){ return Math.floor((firstWeekday(y,m) + d - 1) / 7); }
  function parseKey(k){ var p = k.split('-'); return new Date(parseInt(p[0],10), parseInt(p[1],10)-1, parseInt(p[2],10)).getTime(); }
  function minToTime(min){ return pad(Math.floor(min/60)) + ':' + pad(min%60); }
  function clamp(v,a,b){ return Math.max(a, Math.min(b, v)); }
  function qclosest(el, sel){ return (el && el.closest) ? el.closest(sel) : null; }
  function escapeHtml(s){ return String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;'); }
  function escapeAttr(s){ return escapeHtml(s).replace(/"/g,'&quot;').replace(/'/g,'&#39;'); }
  function markerIndex(id){ for(var i=0;i<markers.length;i++){ if(markers[i].id===id) return i; } return -1; }
  function findMarker(id){ for(var i=0;i<markers.length;i++){ if(markers[i].id===id) return markers[i]; } return {color:'#999', label:''}; }
  function getStepSize(){ return Math.max(1, state.stepSize || 30); }
  function floorToStep(min){ var s = getStepSize(); return Math.floor(min/s)*s; }
  function getHourPx(){
    if(state.expandMode === 'long'){
      return Math.max(24, Math.round((window.innerHeight * 1.5) / 24));
    }
    return 24;
  }
  function colWeekday(col){
    var p = col.getAttribute('data-date').split('-');
    var d = new Date(parseInt(p[0],10), parseInt(p[1],10)-1, parseInt(p[2],10));
    return WD_FULL[(d.getDay()+6)%7];
  }
  function overlaps(aS,aE,bS,bE){
    if(aS===aE){ return bS <= aS && bE >= aE; }
    if(bS===bE){ return aS <= bS && aE >= bE; }
    return aS < bE && bS < aE;
  }

  function buildWeeks(y, m){
    var weeks = [];
    var total = daysInMonth(y, m);
    var offset = firstWeekday(y, m);
    var week = [];
    var prevTotal = daysInMonth(y, m-1);
    for(var i=0;i<offset;i++){
      week.push({ date: new Date(y, m-1, prevTotal - offset + i + 1), inMonth:false });
    }
    for(var d=1; d<=total; d++){
      week.push({ date: new Date(y, m, d), inMonth:true });
      if(week.length===7){ weeks.push(week); week=[]; }
    }
    if(week.length>0){
      var nd=1;
      while(week.length<7){ week.push({ date: new Date(y, m+1, nd++), inMonth:false }); }
      weeks.push(week);
    }
    return weeks;
  }

  function normalize(){
    while(state.month<0){ state.month += 12; state.year--; }
    while(state.month>11){ state.month -= 12; state.year++; }
  }

  /* ---------- 渲染 ---------- */
  function syncHeaders(){
    document.getElementById('currentLabel').textContent = '当前月份：' + state.year + '年' + (state.month+1) + '月';
    document.getElementById('calTitle').textContent = state.year + '年' + (state.month+1) + '月';
    document.getElementById('yearText').textContent = state.selYear + '年';
  }

  function renderWeekdays(){
    var el = document.getElementById('weekdays');
    var html = '<div class="expand-spacer"></div>';
    for(var i=0;i<7;i++) html += '<div class="wd">' + WD[i] + '</div>';
    html += '<div class="expand-spacer"></div>';
    el.innerHTML = html;
  }

  function renderMonthSelector(){
    var cap = document.getElementById('monthCapsule');
    var todayMonth = new Date().getMonth();
    var html = '';
    for(var i=0;i<12;i++){
      var cls = 'month-item';
      if(i === state.month) cls += ' active';
      if(i === todayMonth) cls += ' is-today';
      html += '<div class="' + cls + '" data-month="' + i + '" title="' + (i+1) + '月">' + (i+1) + '</div>';
    }
    cap.innerHTML = html;
  }

  function dateMarkSegments(key){
    var ids = dateMarks[key] || [];
    if(ids.length===0) return '';
    var resolved = [];
    for(var i=0;i<ids.length;i++){ if(markerIndex(ids[i])>=0) resolved.push(ids[i]); }
    resolved.sort(function(a,b){ return markerIndex(a) - markerIndex(b); });
    var shown = resolved.slice(0,3);
    var segs = '';
    for(var j=0;j<shown.length;j++){
      var m = findMarker(shown[j]);
      segs += '<span style="background:' + m.color + '"></span>';
    }
    return segs;
  }

  function renderDateMarks(key){
    var segs = dateMarkSegments(key);
    if(!segs) return '';
    return '<div class="mark-line">' + segs + '</div>';
  }

  function renderTimeMarksForDay(key){
    var arr = timeMarks[key] || [];
    var html = '';
    for(var i=0;i<arr.length;i++){
      var m = arr[i];
      var hourPx = getHourPx();
      var top = (m.startMin/60) * hourPx;
      var sel = (state.selectedTimeMarkId === m.id);
      var handles = sel ? '<div class="mark-handle mark-handle-top" data-edge="top"></div><div class="mark-handle mark-handle-bottom" data-edge="bottom"></div>' : '';
      if(m.endMin === m.startMin){
        html += '<div class="time-mark instant' + (sel?' selected':'') + '" data-tmid="' + m.id + '" style="top:' + (top-1.5) + 'px;background:' + m.color + '" title="' + escapeHtml(m.label) + ' ' + minToTime(m.startMin) + '">' + handles + '</div>';
      } else {
        var hgt = ((m.endMin - m.startMin)/60) * hourPx;
        html += '<div class="time-mark' + (sel?' selected':'') + '" data-tmid="' + m.id + '" style="top:' + top + 'px;height:' + Math.max(4,hgt) + 'px;background:' + m.color + '" title="' + escapeHtml(m.label) + ' ' + minToTime(m.startMin) + '-' + minToTime(m.endMin) + '">' + handles + '</div>';
      }
    }
    return html;
  }

  function renderWeekRow(week, wi){
    var todayKey = fmtDate(new Date());
    var cells = '';
    for(var i=0;i<week.length;i++){
      var d = week[i];
      var key = fmtDate(d.date);
      var cls = 'day-cell';
      if(!d.inMonth) cls += ' other-month';
      if(key===todayKey) cls += ' today';
      if(state.selectedDates.has(key)) cls += ' selected';
      var hasTime = (timeMarks[key] && timeMarks[key].length > 0);
      cells += '<div class="' + cls + '" data-date="' + key + '">'
        + (hasTime ? '<span class="time-badge" title="该日期有时间段标记"></span>' : '')
        + '<div class="day-num">' + d.date.getDate() + '</div>'
        + renderDateMarks(key)
        + '</div>';
    }
    return '<div class="week-row" data-week="' + wi + '">'
      + '<button class="expand-btn" data-week="' + wi + '" title="展开/收起本周"><span class="chev">&#9650;</span><span class="chev">&#9660;</span></button>'
      + cells
      + '<button class="expand-btn" data-week="' + wi + '" title="展开/收起本周"><span class="chev">&#9650;</span><span class="chev">&#9660;</span></button>'
      + '</div>';
  }

  function getNowTop(){
    var n = new Date();
    return (n.getHours()*60 + n.getMinutes()) / 60 * getHourPx();
  }

  function renderDetailPanel(week, wi){
    var todayKey = fmtDate(new Date());
    var hourPx = getHourPx();
    var totalH = hourPx * 24;
    var nowTop = getNowTop();
    var heads = '';
    var cols = '';
    currentWeek = [];
    for(var i=0;i<week.length;i++){
      var d = week[i];
      var key = fmtDate(d.date);
      currentWeek.push(key);
      var isToday = (key===todayKey);
      var segs = dateMarkSegments(key);
      var markHtml = segs ? '<div class="mark-line">' + segs + '</div>' : '';
      heads += '<div class="detail-day-head' + (isToday?' today':'') + '" data-date="' + key + '">'
        + '<span>' + d.date.getDate() + '</span>'
        + '<span class="wd">' + WD_FULL[i] + '</span>'
        + markHtml
        + '</div>';
      cols += '<div class="time-col" data-date="' + key + '" style="--hour-h:' + hourPx + 'px">'
        + renderTimeMarksForDay(key)
        + (isToday ? '<div class="now-line" style="top:' + nowTop + 'px"></div>' : '')
        + '</div>';
    }
    var labels = '';
    for(var h=0; h<=24; h++){
      var tf = (h===24) ? 'translateY(-100%)' : 'translateY(-50%)';
      labels += '<div class="tlabel" style="top:' + (h*hourPx) + 'px; transform:' + tf + '">' + h + '点</div>';
    }
    var animCls = state.detailJustExpanded ? ' detail-anim' : '';
    return '<div class="week-row detail-row' + animCls + '" data-week="' + wi + '">'
      + '<button class="expand-btn active detail-left" data-week="' + wi + '" title="收起本周"><span class="chev">&#9660;</span><span class="chev">&#9650;</span></button>'
      + '<div class="detail-axis">'
        + '<div class="axis-spacer-top"></div>'
        + '<div class="axis-body">' + labels + '</div>'
      + '</div>'
      + '<div class="detail-panel">'
        + '<div class="detail-heads-row">' + heads + '</div>'
        + '<div class="detail-body-row" id="detailBody" style="height:' + totalH + 'px">' + cols + '<div class="pending-sel" id="pendingSel"></div>' + '</div>'
      + '</div>'
      + '<button class="expand-btn active" data-week="' + wi + '" title="收起本周"><span class="chev">&#9660;</span><span class="chev">&#9650;</span></button>'
      + '</div>';
  }

  function renderMonth(){
    var weeks = buildWeeks(state.year, state.month);
    var grid = document.getElementById('monthGrid');
    var html = '';
    if(state.expandedWeekIndex !== null && state.expandedWeekIndex < weeks.length){
      var wi = state.expandedWeekIndex;
      if(wi > 0) html += renderWeekRow(weeks[wi-1], wi-1);
      html += renderDetailPanel(weeks[wi], wi);
      if(wi < weeks.length-1) html += renderWeekRow(weeks[wi+1], wi+1);
    } else {
      for(var i=0;i<weeks.length;i++) html += renderWeekRow(weeks[i], i);
    }
    grid.innerHTML = html;
    state.detailJustExpanded = false;
    if(state.expandedWeekIndex !== null){
      bindDetailEvents();
    } else {
      hideTooltip();
    }
    updatePendingSel();
    updateStepPanelVisibility();
  }

  function renderMarkers(){
    var list = document.getElementById('markerList');
    var html = '';
    for(var i=0;i<markers.length;i++){
      var m = markers[i];
      html += '<div class="marker-item' + (m.id===state.selectedMarkerId?' active':'') + '" draggable="true" data-id="' + m.id + '">'
        + '<span class="drag-handle">&#8942;&#8942;</span>'
        + '<span class="color-dot" style="background:' + m.color + '"></span>'
        + '<span class="marker-label">' + escapeHtml(m.label) + '</span>'
        + '<button class="marker-del" data-id="' + m.id + '" title="删除">&#10005;</button>'
        + '</div>';
    }
    if(markers.length===0){
      html = '<div class="empty-hint">暂无标记色<br>点击右下角 + 添加</div>';
    }
    list.innerHTML = html;
    bindMarkerEvents();
  }

  function renderAll(){
    renderWeekdays();
    renderMonthSelector();
    syncHeaders();
    renderMonth();
    renderMarkers();
    updateToolbar();
    updateMarkBlocks();
    renderCalSwitcher();
  }

  /* 已选中的时间段标记：只有在周展开视图里才算「有效选中」 */
  function hasSelectedTimeMark(){
    return state.expandedWeekIndex !== null && !!state.selectedTimeMarkId && !!findTimeMark(state.selectedTimeMarkId);
  }

  function updateToolbar(){
    var markBtn = document.getElementById('markBtn');
    var clearBtn = document.getElementById('clearBtn');
    var hasSel = state.selectedDates.size>0 || !!state.pendingTime;
    var canMark = !!state.selectedMarkerId && hasSel;
    var canClear = hasSel || hasSelectedTimeMark();
    markBtn.style.display = canMark ? 'inline-block' : 'none';
    clearBtn.style.display = canClear ? 'inline-block' : 'none';
  }

  function updateMarkBlocks(){
    var container = document.getElementById('markBlocks');
    var ids = new Set();
    state.selectedDates.forEach(function(k){
      var arr = dateMarks[k] || [];
      arr.forEach(function(id){ ids.add(id); });
    });
    var html = '';
    for(var i=0;i<markers.length;i++){
      var m = markers[i];
      if(ids.has(m.id)){
        html += '<span class="mark-block" data-id="' + m.id + '" title="' + escapeHtml(m.label) + '">'
          + '<span class="mark-block-dot" style="background:' + m.color + '"></span>'
          + '<span>' + escapeHtml(m.label) + '</span>'
          + '<button class="mark-block-x" data-id="' + m.id + '" title="移除该标记">&#10005;</button>'
          + '</span>';
      }
    }
    container.innerHTML = html;
  }

  function updatePendingSel(){
    var ov = document.getElementById('pendingSel');
    var body = document.getElementById('detailBody');
    if(!ov || !body) return;
    var p = state.pendingTime;
    if(!p){ ov.style.display = 'none'; return; }
    var col = body.querySelector('.time-col[data-date="' + p.dateKey + '"]');
    if(!col){ ov.style.display = 'none'; return; }
    var bodyRect = body.getBoundingClientRect();
    var colRect = col.getBoundingClientRect();
    var left = colRect.left - bodyRect.left;
    var topPx = (p.startMin/1440) * colRect.height;
    var hPx = ((p.endMin - p.startMin)/1440) * colRect.height;
    ov.style.display = 'block';
    ov.style.left = left + 'px';
    ov.style.width = colRect.width + 'px';
    ov.style.top = topPx + 'px';
    ov.style.height = Math.max(2, hPx) + 'px';
  }

  function updateStepPanelVisibility(){
    var p = document.getElementById('stepPanel');
    if(p) p.style.display = (state.expandedWeekIndex !== null) ? 'block' : 'none';
  }

  /* ---------- 日期选择（单击 / Shift+点击添加 / 左键滑动连续选中） ---------- */
  function selectSingle(key, additive){
    if(additive){
      state.selectedDates = new Set(state.selectedDates);
      state.selectedDates.add(key);
    } else {
      state.selectedDates = new Set([key]);
    }
    state.anchorDate = key;
    renderMonth();
    updateToolbar();
    updateMarkBlocks();
  }

  function beginDateDrag(key, additive){
    dateDrag.active = true;
    dateDrag.anchor = key;
    dateDrag.additive = additive;
    dateDrag.lastKey = key;
    if(additive){
      state.selectedDates = new Set(state.selectedDates);
      state.selectedDates.add(key);
    } else {
      state.selectedDates = new Set([key]);
    }
    state.anchorDate = key;
    applySelectionToDOM();
    updateToolbar();
    updateMarkBlocks();
  }

  function moveDateDrag(hoverKey){
    if(!dateDrag.active) return;
    if(hoverKey === dateDrag.lastKey) return;
    dateDrag.lastKey = hoverKey;
    var set = dateDrag.additive ? new Set(state.selectedDates) : new Set();
    var a = parseKey(dateDrag.anchor);
    var b = parseKey(hoverKey);
    if(a>b){ var t=a; a=b; b=t; }
    for(var t2=a; t2<=b; t2+=86400000){ set.add(fmtDate(new Date(t2))); }
    state.selectedDates = set;
    applySelectionToDOM();
    updateToolbar();
    updateMarkBlocks();
  }

  function endDateDrag(){
    if(!dateDrag.active) return;
    dateDrag.active = false;
    dateDrag.lastKey = null;
    renderMonth();
    updateToolbar();
    updateMarkBlocks();
  }

  function applySelectionToDOM(){
    var grid = document.getElementById('monthGrid');
    var cells = grid.querySelectorAll('.day-cell');
    for(var i=0;i<cells.length;i++){
      var c = cells[i];
      var key = c.getAttribute('data-date');
      if(state.selectedDates.has(key)) c.classList.add('selected');
      else c.classList.remove('selected');
    }
  }

  /* ---------- 月份切换 ---------- */
  function changeMonth(delta, animate){
    if(animate){ if(animating) return; animateSwitch(delta); }
    else { applyMonthDelta(delta); }
  }

  function applyMonthDelta(delta){
    state.month += delta;
    normalize();
    state.selYear = state.year;
    state.expandedWeekIndex = null;
    state.pendingTime = null;
    renderAll();
  }

  function animateSwitch(dir){
    animating = true;
    var grid = document.getElementById('monthGrid');
    grid.style.transition = 'transform 0.15s ease, opacity 0.15s ease';
    grid.style.transform = 'translateX(' + (dir * -40) + 'px)';
    grid.style.opacity = '0';
    setTimeout(function(){
      state.month += dir;
      normalize();
      state.selYear = state.year;
      state.expandedWeekIndex = null;
      state.pendingTime = null;
      renderAll();
      grid.style.transition = 'none';
      grid.style.transform = 'translateX(' + (dir * 40) + 'px)';
      grid.style.opacity = '0';
      void grid.offsetWidth;
      grid.style.transition = 'transform 0.15s ease, opacity 0.15s ease';
      grid.style.transform = 'translateX(0)';
      grid.style.opacity = '1';
      setTimeout(function(){ animating = false; }, 160);
    }, 150);
  }

  function animateYearJump(){
    if(animating) return;
    animating = true;
    var dir = (state.selYear >= state.year) ? 1 : -1;
    var grid = document.getElementById('monthGrid');
    grid.style.transition = 'transform 0.18s ease, opacity 0.18s ease';
    grid.style.transform = 'translateY(' + (dir * -18) + 'px)';
    grid.style.opacity = '0';
    setTimeout(function(){
      state.year = state.selYear;
      state.expandedWeekIndex = null;
      state.pendingTime = null;
      renderAll();
      grid.style.transition = 'none';
      grid.style.transform = 'translateY(' + (dir * 18) + 'px)';
      grid.style.opacity = '0';
      void grid.offsetWidth;
      grid.style.transition = 'transform 0.18s ease, opacity 0.18s ease';
      grid.style.transform = 'translateY(0)';
      grid.style.opacity = '1';
      setTimeout(function(){ animating = false; }, 200);
    }, 180);
  }

  function collapseWeek(){
    hideTooltip();
    var row = document.querySelector('.detail-row');
    if(row){
      row.classList.add('detail-collapse');
      setTimeout(function(){
        state.expandedWeekIndex = null;
        state.pendingTime = null;
        renderMonth();
        updateToolbar();
      }, 170);
    } else {
      state.expandedWeekIndex = null;
      state.pendingTime = null;
      renderMonth();
      updateToolbar();
    }
  }

  /* Tab：展开 / 收起「当前选中日期所在的一周」（没有选中日期时以今天为准），并自动跳到对应月份 */
  function handleTabExpand(){
    var key = state.anchorDate || fmtDate(new Date());
    var p = key.split('-');
    var y = parseInt(p[0],10), m = parseInt(p[1],10)-1, d = parseInt(p[2],10);
    var needJump = (state.year !== y || state.month !== m);
    if(needJump){
      state.year = y; state.month = m; state.selYear = y;
    }
    var wi = weekIndexFor(y, m, d);
    if(wi < 0) return;

    /* 这一周已经展开着 -> 再按一次就收起 */
    if(!needJump && state.expandedWeekIndex === wi){
      collapseWeek();
      return;
    }

    state.expandedWeekIndex = wi;
    state.pendingTime = null;
    state.detailJustExpanded = true;
    renderAll();
    updateToolbar();
  }

  /* ---------- 标记 / 消除 ---------- */
  function applyMark(){
    var marker = null;
    for(var i=0;i<markers.length;i++){ if(markers[i].id===state.selectedMarkerId){ marker=markers[i]; break; } }
    if(!marker) return;

    if(state.pendingTime){
      var p = state.pendingTime;
      if(!timeMarks[p.dateKey]) timeMarks[p.dateKey] = [];
      timeMarks[p.dateKey].push({ id:'tm'+Date.now(), markerId:marker.id, color:marker.color, label:marker.label, startMin:p.startMin, endMin:p.endMin });
      state.pendingTime = null;
      renderMonth();
      updateToolbar();
      save();
      return;
    }

    if(state.selectedDates.size>0){
      state.selectedDates.forEach(function(k){
        if(!dateMarks[k]) dateMarks[k] = [];
        if(dateMarks[k].indexOf(marker.id) === -1) dateMarks[k].push(marker.id);
      });
      renderMonth();
      updateToolbar();
      updateMarkBlocks();
      save();
    }
  }

  function applyClear(){
    /* 1) 左键选中了某个时间段标记 -> 直接删掉它 */
    if(hasSelectedTimeMark()){
      var selId = state.selectedTimeMarkId;
      var selKey = findTimeMarkDateKey(selId);
      if(selKey){
        var selArr = timeMarks[selKey] || [];
        timeMarks[selKey] = selArr.filter(function(m){ return m.id !== selId; });
        if(timeMarks[selKey].length === 0){ delete timeMarks[selKey]; }
      }
      state.selectedTimeMarkId = null;
      closeValueEditor();
      renderMonth();
      updateToolbar();
      save();
      return;
    }
    /* 2) 正在框选的时间段 -> 清除与之重叠的标记 */
    if(state.pendingTime){
      var p = state.pendingTime;
      var arr = timeMarks[p.dateKey] || [];
      timeMarks[p.dateKey] = arr.filter(function(m){
        return !overlaps(p.startMin, p.endMin, m.startMin, m.endMin);
      });
      if(timeMarks[p.dateKey].length===0) delete timeMarks[p.dateKey];
      state.pendingTime = null;
      renderMonth();
      updateToolbar();
      save();
      return;
    }
    if(state.selectedDates.size>0){
      state.selectedDates.forEach(function(k){ delete dateMarks[k]; });
      renderMonth();
      updateToolbar();
      updateMarkBlocks();
      save();
    }
  }

  /* ---------- 周详情：时间轴拖选 / tooltip ---------- */
  function pointerToMinute(e, col){
    var rect = col.getBoundingClientRect();
    var y = clamp(e.clientY - rect.top, 0, rect.height);
    return Math.round(y / rect.height * 1440);
  }

  function showTooltip(e, col){
    var min = pointerToMinute(e, col);
    var showMin = e.shiftKey ? floorToStep(min) : min;
    var tip = document.getElementById('timeTooltip');
    tip.textContent = colWeekday(col) + ' ' + minToTime(showMin);
    tip.style.left = (e.clientX + 14) + 'px';
    tip.style.top = (e.clientY - 6) + 'px';
    tip.style.display = 'block';
  }

  function hideTooltip(){
    var tip = document.getElementById('timeTooltip');
    if(tip) tip.style.display = 'none';
  }

  /* ---------- 标记块：选中 / 长按移动 / 边界缩放 ---------- */
  function findTimeMarkDateKey(id){
    var keys = Object.keys(timeMarks);
    for(var i=0;i<keys.length;i++){
      var arr = timeMarks[keys[i]];
      for(var j=0;j<arr.length;j++){ if(arr[j].id === id) return keys[i]; }
    }
    return null;
  }

  function selectTimeMark(id){
    state.selectedTimeMarkId = id;
    renderMonth();
    updateToolbar();
  }

  function clearMarkSelectionDOM(){
    if(!state.selectedTimeMarkId) return;
    var el = document.querySelector('.time-mark.selected');
    if(el){
      el.classList.remove('selected');
      var hs = el.querySelectorAll('.mark-handle');
      for(var i=0;i<hs.length;i++){ if(hs[i].parentNode) hs[i].parentNode.removeChild(hs[i]); }
    }
    state.selectedTimeMarkId = null;
  }

  function showPressProgress(x, y){
    var el = document.getElementById('pressProgress');
    if(!el) return;
    el.style.left = x + 'px';
    el.style.top = y + 'px';
    el.style.display = 'block';
    el.style.animation = 'none';
    void el.offsetWidth;
    el.style.animation = '';
  }

  function hidePressProgress(){
    var el = document.getElementById('pressProgress');
    if(el) el.style.display = 'none';
  }

  function cancelPressHold(){
    markDrag.pressPending = false;
    clearTimeout(markDrag.pressTimer);
    clearTimeout(markDrag.progressTimer);
    hidePressProgress();
  }

  function beginPressHold(markId, e){
    cancelPressHold();
    markDrag.pressId = markId;
    markDrag.pressX = e.clientX;
    markDrag.pressY = e.clientY;
    markDrag.pressPending = true;
    markDrag.pressTimer = setTimeout(function(){
      showPressProgress(markDrag.pressX, markDrag.pressY);
      markDrag.progressTimer = setTimeout(function(){
        hidePressProgress();
        beginMarkMove(markDrag.pressId, markDrag.pressX, markDrag.pressY);
      }, 800);
    }, 220);
  }

  function beginMarkMove(markId, x, y){
    var tm = findTimeMark(markId);
    if(!tm) return;
    var dk = findTimeMarkDateKey(markId);
    if(!dk) return;
    var colEl = document.querySelector('.time-col[data-date="' + dk + '"]');
    if(!colEl) return;
    var rect = colEl.getBoundingClientRect();
    var oi = currentWeek.indexOf(dk);
    if(oi < 0) return;
    markDrag.active = true;
    markDrag.mode = 'move';
    markDrag.markId = markId;
    markDrag.dateKey = dk;
    markDrag.origStart = tm.startMin;
    markDrag.origEnd = tm.endMin;
    markDrag.curStart = tm.startMin;
    markDrag.curEnd = tm.endMin;
    markDrag.origColIdx = oi;
    markDrag.curColIdx = oi;
    markDrag.startX = x;
    markDrag.startY = y;
    markDrag.colH = rect.height || 576;
    markDrag.colW = rect.width || 40;
    markDrag.pressPending = false;
    document.body.classList.add('mark-moving');
  }

  function beginMarkResize(markEl, edge, e, col){
    var tm = findTimeMark(markEl.getAttribute('data-tmid'));
    if(!tm) return;
    var rect = col.getBoundingClientRect();
    cancelPressHold();
    markDrag.active = true;
    markDrag.mode = (edge === 'top') ? 'resize-top' : 'resize-bottom';
    markDrag.markId = tm.id;
    markDrag.dateKey = col.getAttribute('data-date');
    markDrag.origStart = tm.startMin;
    markDrag.origEnd = tm.endMin;
    markDrag.curStart = tm.startMin;
    markDrag.curEnd = tm.endMin;
    markDrag.startY = e.clientY;
    markDrag.startX = e.clientX;
    markDrag.colH = rect.height || 576;
  }

  function updateMarkDrag(e){
    if(!markDrag.active) return;
    var ppm = 1440 / (markDrag.colH || 576);
    if(markDrag.mode === 'move'){
      var dy = e.clientY - markDrag.startY;
      var dm = Math.round(dy * ppm);
      if(e.shiftKey){ var s = getStepSize(); dm = Math.round(dm / s) * s; }
      var dur = markDrag.origEnd - markDrag.origStart;
      var ns = clamp(markDrag.origStart + dm, 0, 1440 - dur);
      markDrag.curStart = ns;
      markDrag.curEnd = ns + dur;
      var dx = e.clientX - markDrag.startX;
      var shiftCols = Math.round(dx / (markDrag.colW || 40));
      markDrag.curColIdx = clamp(markDrag.origColIdx + shiftCols, 0, currentWeek.length - 1);
    } else if(markDrag.mode === 'resize-top'){
      var dm2 = Math.round((e.clientY - markDrag.startY) * ppm);
      if(e.shiftKey){ var s2 = getStepSize(); dm2 = Math.round(dm2 / s2) * s2; }
      markDrag.curStart = clamp(markDrag.origStart + dm2, 0, markDrag.origEnd - 1);
      markDrag.curEnd = markDrag.origEnd;
    } else if(markDrag.mode === 'resize-bottom'){
      var dm3 = Math.round((e.clientY - markDrag.startY) * ppm);
      if(e.shiftKey){ var s3 = getStepSize(); dm3 = Math.round(dm3 / s3) * s3; }
      markDrag.curStart = markDrag.origStart;
      markDrag.curEnd = clamp(markDrag.origEnd + dm3, markDrag.origStart + 1, 1440);
    }
    paintMarkDrag();
  }

  function paintMarkDrag(){
    var el = document.querySelector('.time-mark[data-tmid="' + markDrag.markId + '"]');
    if(!el) return;
    var pxPerMin = getHourPx() / 60;
    el.style.top = (markDrag.curStart * pxPerMin) + 'px';
    el.style.height = Math.max(4, (markDrag.curEnd - markDrag.curStart) * pxPerMin) + 'px';
    if(markDrag.mode === 'move'){
      var targetKey = currentWeek[markDrag.curColIdx];
      var targetCol = document.querySelector('.time-col[data-date="' + targetKey + '"]');
      if(targetCol && el.parentNode !== targetCol){ targetCol.appendChild(el); }
    }
  }

  function endMarkDrag(){
    if(!markDrag.active) return;
    markDrag.active = false;
    document.body.classList.remove('mark-moving');
    var id = markDrag.markId;
    var tm = findTimeMark(id);
    if(tm){
      tm.startMin = markDrag.curStart;
      tm.endMin = markDrag.curEnd;
      if(markDrag.mode === 'move'){
        var newKey = currentWeek[markDrag.curColIdx];
        var oldKey = markDrag.dateKey;
        if(newKey && newKey !== oldKey){
          var oa = timeMarks[oldKey] || [];
          for(var i=0;i<oa.length;i++){ if(oa[i].id === id){ oa.splice(i,1); break; } }
          if(oa.length === 0) delete timeMarks[oldKey];
          if(!timeMarks[newKey]) timeMarks[newKey] = [];
          timeMarks[newKey].push(tm);
        }
      }
      save();
    }
    renderMonth();
  }

  function bindDetailEvents(){
    var body = document.getElementById('detailBody');
    if(!body) return;
    var cols = body.querySelectorAll('.time-col');
    for(var i=0;i<cols.length;i++){
      (function(col){
        col.addEventListener('pointerdown', function(e){
          if(e.button !== 0) return;
          var markEl = qclosest(e.target, '.time-mark');
          if(markEl && !e.ctrlKey && !e.metaKey){
            e.preventDefault();
            var handle = qclosest(e.target, '.mark-handle');
            if(handle){
              beginMarkResize(markEl, handle.getAttribute('data-edge'), e, col);
            } else {
              selectTimeMark(markEl.getAttribute('data-tmid'));
              beginPressHold(markEl.getAttribute('data-tmid'), e);
            }
            return;
          }
          e.preventDefault();
          clearMarkSelectionDOM();
          detailDrag.active = true;
          detailDrag.col = col;
          detailDrag.shift = e.shiftKey;
          var key = col.getAttribute('data-date');
          var min = pointerToMinute(e, col);
          var s = getStepSize();
          if(e.shiftKey){
            var snap = floorToStep(min);
            detailDrag.anchor = snap;
            state.pendingTime = { dateKey:key, startMin:snap, endMin:snap + s };
          } else {
            detailDrag.anchor = min;
            state.pendingTime = { dateKey:key, startMin:min, endMin:min };
          }
          try { col.setPointerCapture(e.pointerId); } catch(err){}
          updatePendingSel();
          updateToolbar();
          showTooltip(e, col);
        });

        col.addEventListener('pointermove', function(e){
          var min = pointerToMinute(e, col);
          if(detailDrag.active && detailDrag.col === col){
            var s = getStepSize();
            var key = col.getAttribute('data-date');
            if(detailDrag.shift){
              var cur = floorToStep(min);
              var lo = Math.min(detailDrag.anchor, cur);
              var hi = Math.max(detailDrag.anchor, cur);
              state.pendingTime = { dateKey:key, startMin:lo, endMin:hi + s };
            } else {
              var a = detailDrag.anchor;
              state.pendingTime = { dateKey:key, startMin:Math.min(a,min), endMin:Math.max(a,min) };
            }
            updatePendingSel();
            updateToolbar();
          }
          showTooltip(e, col);
        });

        col.addEventListener('pointerup', function(e){
          if(detailDrag.active && detailDrag.col === col){
            detailDrag.active = false;
            detailDrag.col = null;
            updateToolbar();
          }
        });

        col.addEventListener('pointercancel', function(){
          if(detailDrag.active && detailDrag.col === col){ detailDrag.active = false; detailDrag.col = null; }
        });

        col.addEventListener('pointerleave', function(){
          if(!detailDrag.active) hideTooltip();
        });
      })(cols[i]);
    }
  }

  /* ---------- 标记色列表 ---------- */
  function setDropLine(item, before){
    var list = document.getElementById('markerList');
    var line = document.getElementById('dropLine');
    if(!line){
      line = document.createElement('div');
      line.id = 'dropLine';
      line.className = 'drop-line';
    }
    if(line.parentNode) line.parentNode.removeChild(line);
    if(before){ list.insertBefore(line, item); }
    else { list.insertBefore(line, item.nextSibling); }
  }

  function clearDropLine(){
    var line = document.getElementById('dropLine');
    if(line && line.parentNode) line.parentNode.removeChild(line);
  }

  function bindMarkerEvents(){
    var list = document.getElementById('markerList');
    var items = list.querySelectorAll('.marker-item');
    for(var i=0;i<items.length;i++){
      (function(item){
        item.addEventListener('click', function(e){
          if(qclosest(e.target, '.marker-del')) return;
          var id = parseInt(item.getAttribute('data-id'), 10);
          state.selectedMarkerId = (state.selectedMarkerId === id) ? null : id;
          renderMarkers();
          updateToolbar();
        });
        item.addEventListener('dblclick', function(e){
          if(qclosest(e.target, '.marker-del')) return;
          openEditModal(item.getAttribute('data-id'));
        });
        item.addEventListener('dragstart', function(e){
          e.dataTransfer.setData('text/plain', item.getAttribute('data-id'));
          e.dataTransfer.effectAllowed = 'move';
          item.classList.add('dragging');
        });
        item.addEventListener('dragend', function(){
          item.classList.remove('dragging');
          clearDropLine();
        });
        item.addEventListener('dragover', function(e){
          e.preventDefault();
          e.stopPropagation();
          e.dataTransfer.dropEffect = 'move';
          var rect = item.getBoundingClientRect();
          var before = (e.clientY - rect.top) < (rect.height / 2);
          dragTarget = { id: item.getAttribute('data-id'), before: before };
          setDropLine(item, before);
        });
        item.addEventListener('drop', function(e){
          e.preventDefault();
          e.stopPropagation();
          var fromId = parseInt(e.dataTransfer.getData('text/plain'), 10);
          clearDropLine();
          if(dragTarget.id){
            reorderMarkers(fromId, dragTarget.id, dragTarget.before);
          }
          dragTarget = { id:null, before:true };
        });
        var del = item.querySelector('.marker-del');
        if(del){
          del.addEventListener('click', function(e){
            e.stopPropagation();
            deleteMarker(del.getAttribute('data-id'));
          });
        }
      })(items[i]);
    }
  }

  function reorderMarkers(fromId, toId, before){
    fromId = parseInt(fromId, 10);
    toId = parseInt(toId, 10);
    var from=-1, to=-1;
    for(var i=0;i<markers.length;i++){
      if(markers[i].id===fromId) from=i;
      if(markers[i].id===toId) to=i;
    }
    if(from<0 || to<0 || from===to) return;
    var insertIndex = before ? to : to + 1;
    var moved = markers.splice(from,1)[0];
    if(from < insertIndex) insertIndex -= 1;
    markers.splice(insertIndex,0,moved);
    renderMarkers();
    renderMonth();
    save();
  }

  function deleteMarker(id){
    id = parseInt(id, 10);
    var removed = null;
    for(var mi=0; mi<markers.length; mi++){ if(markers[mi].id === id){ removed = markers[mi]; break; } }
    markers = markers.filter(function(m){ return m.id !== id; });
    if(state.selectedMarkerId===id) state.selectedMarkerId=null;

    /* 日期标记 */
    var keys = Object.keys(dateMarks);
    for(var i=0;i<keys.length;i++){
      var k = keys[i];
      dateMarks[k] = dateMarks[k].filter(function(x){ return x !== id; });
      if(dateMarks[k].length===0) delete dateMarks[k];
    }

    /* 日期标记上保存的数值 */
    var vkeys = Object.keys(dateMarkValues);
    for(var v=0; v<vkeys.length; v++){
      var parts = vkeys[v].split('|');
      if(parts.length >= 2 && parseInt(parts[parts.length-1], 10) === id){ delete dateMarkValues[vkeys[v]]; }
    }

    /* 展开后时间段上的标记：优先按 markerId 精确删除；
       旧数据没有记录 markerId，则用「颜色 + 含义」匹配后一并删除 */
    var tmKeys = Object.keys(timeMarks);
    for(var t=0; t<tmKeys.length; t++){
      var dk = tmKeys[t];
      var arr = timeMarks[dk] || [];
      timeMarks[dk] = arr.filter(function(tm){
        if(!tm) return false;
        if(tm.markerId !== undefined && tm.markerId !== null){ return Number(tm.markerId) !== id; }
        if(!removed){ return true; }
        return !(tm.color === removed.color && (tm.label || '') === (removed.label || ''));
      });
      if(timeMarks[dk].length === 0){ delete timeMarks[dk]; }
    }
    if(state.selectedTimeMarkId && !findTimeMark(state.selectedTimeMarkId)){ state.selectedTimeMarkId = null; }
    closeValueEditor();

    renderMarkers();
    renderMonth();
    updateToolbar();
    updateMarkBlocks();
    save();
  }

  /* 编辑标记色后，让已存在的时间段标记跟随新的颜色 / 含义 */
  function syncTimeMarksForMarker(marker, oldColor, oldLabel){
    var keys = Object.keys(timeMarks);
    var touched = false;
    for(var i=0;i<keys.length;i++){
      var arr = timeMarks[keys[i]] || [];
      for(var j=0;j<arr.length;j++){
        var tm = arr[j];
        if(!tm) continue;
        var linked = (tm.markerId !== undefined && tm.markerId !== null)
          ? Number(tm.markerId) === marker.id
          : (tm.color === oldColor && (tm.label || '') === (oldLabel || ''));
        if(linked){
          tm.markerId = marker.id;
          tm.color = marker.color;
          tm.label = marker.label;
          touched = true;
        }
      }
    }
    return touched;
  }

  /* ---------- 弹窗 ---------- */
  function renderPresets(){
    var container = document.getElementById('presetColors');
    var html = '';
    for(var i=0;i<PRESETS.length;i++){
      html += '<button type="button" class="preset-swatch" data-color="' + PRESETS[i][0] + '" data-label="' + PRESETS[i][1] + '" title="' + PRESETS[i][1] + '" style="background:' + PRESETS[i][0] + '"></button>';
    }
    container.innerHTML = html;
    var swatches = container.querySelectorAll('.preset-swatch');
    for(var j=0;j<swatches.length;j++){
      swatches[j].addEventListener('click', function(e){
        var sw = e.target;
        tempColor = sw.getAttribute('data-color');
        document.getElementById('customColor').value = tempColor;
        document.getElementById('colorPreview').style.background = tempColor;
        var mi = document.getElementById('markerMeaning');
        if(mi.value.trim() === ''){ mi.value = sw.getAttribute('data-label'); }
        var all = container.querySelectorAll('.preset-swatch');
        for(var k=0;k<all.length;k++) all[k].classList.remove('selected');
        sw.classList.add('selected');
      });
    }
  }

  function clearPresetSelection(){
    var all = document.querySelectorAll('.preset-swatch');
    for(var k=0;k<all.length;k++) all[k].classList.remove('selected');
  }

  function openModal(){
    editingMarkerId = null;
    tempColor = '#3b82f6';
    document.getElementById('customColor').value = tempColor;
    document.getElementById('colorPreview').style.background = tempColor;
    document.getElementById('markerMeaning').value = '';
    document.getElementById('modalTitle').textContent = '添加标记色';
    renderPresets();
    document.getElementById('modalOverlay').classList.add('show');
    document.getElementById('markerMeaning').focus();
  }

  function openEditModal(id){
    id = parseInt(id, 10);
    if(markerIndex(id) < 0) return;
    var m = findMarker(id);
    editingMarkerId = id;
    tempColor = m.color;
    document.getElementById('customColor').value = m.color;
    document.getElementById('colorPreview').style.background = m.color;
    document.getElementById('markerMeaning').value = m.label;
    document.getElementById('modalTitle').textContent = '编辑标记色';
    renderPresets();
    highlightPresetByColor(m.color);
    document.getElementById('modalOverlay').classList.add('show');
    document.getElementById('markerMeaning').focus();
  }

  function highlightPresetByColor(color){
    var swatches = document.querySelectorAll('.preset-swatch');
    for(var i=0;i<swatches.length;i++){
      if(swatches[i].getAttribute('data-color') === color){ swatches[i].classList.add('selected'); }
      else { swatches[i].classList.remove('selected'); }
    }
  }

  function closeModal(){
    document.getElementById('modalOverlay').classList.remove('show');
  }

  function colorName(color){
    for(var i=0;i<PRESETS.length;i++){ if(PRESETS[i][0]===color) return PRESETS[i][1]; }
    return '标记色';
  }

  function confirmAdd(){
    var label = document.getElementById('markerMeaning').value.trim();
    if(!label) label = colorName(tempColor);
    if(editingMarkerId !== null && markerIndex(editingMarkerId) >= 0){
      var m = findMarker(editingMarkerId);
      var oldColor = m.color, oldLabel = m.label;
      m.color = tempColor;
      m.label = label;
      syncTimeMarksForMarker(m, oldColor, oldLabel);
    } else {
      markers.push({ id: ++markerIdCounter, color: tempColor, label: label });
    }
    editingMarkerId = null;
    renderMarkers();
    renderMonth();
    save();
    closeModal();
  }

  /* ---------- 标记数值编辑器 ---------- */
  function findTimeMark(id){
    var keys = Object.keys(timeMarks);
    for(var i=0;i<keys.length;i++){
      var arr = timeMarks[keys[i]];
      for(var j=0;j<arr.length;j++){ if(arr[j].id === id) return arr[j]; }
    }
    return null;
  }

  function getDateMarkValues(dateKey, markerId){
    return dateMarkValues[dateKey + '|' + markerId] || [];
  }

  function setDateMarkValues(dateKey, markerId, vals){
    dateMarkValues[dateKey + '|' + markerId] = vals;
  }

  function cloneValues(v){
    var out = [];
    for(var i=0;i<(v||[]).length;i++){
      var o = { name: v[i].name, kind: v[i].kind || 'slider', value: v[i].value };
      if(o.kind === 'options'){ o.count = v[i].count; o.labels = (v[i].labels||[]).slice(); }
      out.push(o);
    }
    return out;
  }

  function showValuesPanel(x, y){
    var panel = document.getElementById('valuesPanel');
    panel.style.display = 'block';
    var pw = panel.offsetWidth || 340;
    var ph = panel.offsetHeight || 220;
    var left = x + 14;
    var top = y - 8;
    if(left + pw > window.innerWidth - 8){ left = x - pw - 14; }
    if(left < 8){ left = 8; }
    if(top + ph > window.innerHeight - 8){ top = window.innerHeight - ph - 8; }
    if(top < 8){ top = 8; }
    panel.style.left = left + 'px';
    panel.style.top = top + 'px';
  }

  function openValueEditorForDate(key, markerIds, x, y){
    var targets = [];
    for(var i=0;i<markerIds.length;i++){
      var mid = markerIds[i];
      var m = findMarker(mid);
      targets.push({ type:'date', dateKey:key, markerId:mid, label:m.label, color:m.color, values: cloneValues(getDateMarkValues(key, mid)) });
    }
    valueEditor.targets = targets;
    valueEditor.active = 0;
    renderValueEditor();
    showValuesPanel(x, y);
  }

  function openValueEditorForTime(timeId, x, y){
    var tm = findTimeMark(timeId);
    if(!tm) return;
    valueEditor.targets = [{ type:'time', timeId:timeId, label:tm.label, color:tm.color, values: cloneValues(tm.values || []) }];
    valueEditor.active = 0;
    renderValueEditor();
    showValuesPanel(x, y);
  }

  var TYPE_OPTIONS = [
    { key:'slider', label:'百分制（进度条）' },
    { key:'2', label:'二选项（真/假）' },
    { key:'3', label:'三选项（低/中/高）' },
    { key:'4', label:'四选项（低/较低/较高/高）' },
    { key:'5', label:'五选项（低/较低/中/较高/高）' },
    { key:'6', label:'六选项' },
    { key:'7', label:'七选项' }
  ];

  function defaultLabelsForCount(count){
    if(count === 2) return ['真','假'];
    if(count === 3) return ['低','中','高'];
    if(count === 4) return ['低','较低','较高','高'];
    if(count === 5) return ['低','较低','中','较高','高'];
    if(count === 6) return ['很低','低','较低','较高','高','很高'];
    return ['很低','低','较低','中','较高','高','很高'];
  }

  function renderLabelSetOptions(count, currentLabels){
    var presets = optionPresets[String(count)] || [];
    var curKey = (currentLabels || []).join('|');
    var html = '';
    for(var i=0;i<presets.length;i++){
      var key = presets[i].join('|');
      html += '<option value="' + i + '"' + (key === curKey ? ' selected' : '') + '>' + escapeHtml(presets[i].join('/')) + '</option>';
    }
    return html;
  }

  function addValueOfType(key){
    var v;
    if(key === 'slider'){
      v = { name:'数值', kind:'slider', value:50 };
    } else {
      var count = parseInt(key, 10);
      var defs = optionPresets[String(count)] || [];
      var labels = (defs.length > 0) ? defs[0].slice() : defaultLabelsForCount(count);
      v = { name:'数值', kind:'options', count:count, value:0, labels:labels };
    }
    valueEditor.targets[valueEditor.active].values.push(v);
    document.getElementById('valueTypeChooser').style.display = 'none';
    renderValueEditor();
  }

  function renderTypeChooser(){
    var el = document.getElementById('valueTypeChooser');
    var html = '';
    for(var i=0;i<TYPE_OPTIONS.length;i++){
      var tkey = TYPE_OPTIONS[i].key;
      if((tkey === '6' || tkey === '7') && (optionPresets[tkey] || []).length === 0) continue;
      html += '<button class="value-type-btn" data-key="' + tkey + '">' + TYPE_OPTIONS[i].label + '</button>';
    }
    el.innerHTML = html;
    el.style.display = 'flex';
    var btns = el.querySelectorAll('.value-type-btn');
    for(var b=0;b<btns.length;b++){
      btns[b].addEventListener('click', function(e){
        addValueOfType(e.currentTarget.getAttribute('data-key'));
      });
    }
  }

  function renderValueEditor(){
    var targetsEl = document.getElementById('valuesTargets');
    var dotsHtml = '';
    if(valueEditor.targets.length > 1){
      for(var i=0;i<valueEditor.targets.length;i++){
        var t = valueEditor.targets[i];
        dotsHtml += '<button class="value-target-dot' + (i===valueEditor.active?' active':'') + '" data-idx="' + i + '" title="' + escapeHtml(t.label) + '" style="background:' + t.color + '"></button>';
      }
    }
    var act = valueEditor.targets[valueEditor.active];
    targetsEl.innerHTML = '<span class="value-target-label"><span class="color-dot" style="background:' + act.color + '"></span>' + escapeHtml(act.label) + '</span>' + dotsHtml;
    var listEl = document.getElementById('valuesList');
    var vals = act.values;
    var html = '';
    for(var j=0;j<vals.length;j++){
      var v = vals[j];
      var row1 = '<div class="value-row">'
        + '<input type="text" class="value-name" maxlength="20" value="' + escapeHtml(v.name) + '">';
      var row2 = '';
      if(v.kind === 'options'){
        row1 += '<select class="value-labelset" data-idx="' + j + '">' + renderLabelSetOptions(v.count, v.labels) + '</select>';
        var labels = v.labels || [];
        var btns = '';
        for(var b=0;b<labels.length;b++){
          btns += '<button class="opt-btn' + (v.value===b?' active':'') + '" data-idx="' + j + '" data-opt="' + b + '">' + escapeHtml(labels[b]) + '</button>';
        }
        row2 = '<div class="opt-group">' + btns + '</div>';
      } else {
        var vv = (typeof v.value === 'number') ? v.value : 50;
        row2 = '<div class="value-row">'
          + '<input type="range" class="value-range" min="0" max="100" value="' + vv + '">'
          + '<input type="number" class="value-num" min="0" max="100" value="' + vv + '">'
          + '</div>';
      }
      row1 += '<button class="value-del" title="删除">&#10005;</button>' + '</div>';
      html += '<div class="value-item" data-idx="' + j + '">' + row1 + row2 + '</div>';
    }
    if(vals.length === 0){ html = '<div class="empty-hint">点击「+ 添加数值」选择数值类型</div>'; }
    listEl.innerHTML = html;
    bindValueEditorEvents();
  }

  function bindValueEditorEvents(){
    var targetsEl = document.getElementById('valuesTargets');
    var dots = targetsEl.querySelectorAll('.value-target-dot');
    for(var i=0;i<dots.length;i++){
      (function(dot){
        dot.addEventListener('click', function(){
          valueEditor.active = parseInt(dot.getAttribute('data-idx'), 10);
          renderValueEditor();
        });
      })(dots[i]);
    }
    var items = document.querySelectorAll('#valuesList .value-item');
    for(var j=0;j<items.length;j++){
      (function(item, idx){
        var cur = function(){ return valueEditor.targets[valueEditor.active].values[idx]; };
        var nameInp = item.querySelector('.value-name');
        var range = item.querySelector('.value-range');
        var num = item.querySelector('.value-num');
        var del = item.querySelector('.value-del');
        var labelSel = item.querySelector('.value-labelset');
        if(nameInp) nameInp.addEventListener('input', function(){ cur().name = nameInp.value; });
        if(range) range.addEventListener('input', function(){
          var v = parseInt(range.value, 10);
          cur().value = v;
          num.value = v;
        });
        if(num){
          num.addEventListener('input', function(){
            var v = parseInt(num.value, 10);
            if(isNaN(v)) return;
            if(v < 0) v = 0;
            if(v > 100) v = 100;
            num.value = v;
            cur().value = v;
            range.value = v;
          });
          num.addEventListener('change', function(){
            var v = parseInt(num.value, 10);
            if(isNaN(v)) v = 0;
            if(v < 0) v = 0;
            if(v > 100) v = 100;
            num.value = v;
            cur().value = v;
            range.value = v;
          });
        }
        if(labelSel){
          labelSel.addEventListener('change', function(){
            var pi = parseInt(labelSel.value, 10);
            var c = cur().count;
            var ps = optionPresets[String(c)] || [];
            if(ps[pi]){ cur().labels = ps[pi].slice(); }
            renderValueEditor();
          });
        }
        var optBtns = item.querySelectorAll('.opt-btn');
        for(var b=0;b<optBtns.length;b++){
          (function(btn, oi){
            btn.addEventListener('click', function(){ cur().value = oi; renderValueEditor(); });
          })(optBtns[b], b);
        }
        del.addEventListener('click', function(){
          valueEditor.targets[valueEditor.active].values.splice(idx, 1);
          renderValueEditor();
        });
      })(items[j], j);
    }
  }

  function saveValueEditor(){
    for(var i=0;i<valueEditor.targets.length;i++){
      var t = valueEditor.targets[i];
      if(t.type === 'date'){
        setDateMarkValues(t.dateKey, t.markerId, t.values);
      } else if(t.type === 'time'){
        var tm = findTimeMark(t.timeId);
        if(tm) tm.values = t.values;
      }
    }
    save();
  }

  function closeValueEditor(){
    document.getElementById('valuesPanel').style.display = 'none';
  }

  /* ---------- 数据占用 ---------- */
  function fmtSize(bytes){
    if(bytes < 1024) return bytes + ' B';
    var kb = bytes / 1024;
    if(kb < 1024) return kb.toFixed(1) + ' KB';
    return (kb / 1024).toFixed(2) + ' MB';
  }

  /* localStorage 按 UTF-16 计费：字符数 × 2 ≈ 浏览器统计的字节数 */
  function keyBytes(k){
    try{
      var v = localStorage.getItem(k);
      return v ? v.length * 2 : 0;
    }catch(e){ return 0; }
  }
  function keysBytes(list){
    var sum = 0;
    for(var i=0;i<list.length;i++){ sum += keyBytes(list[i]); }
    return sum;
  }
  function totalAppBytes(){
    var sum = 0;
    try{
      for(var i=0;i<localStorage.length;i++){
        var k = localStorage.key(i);
        if(k && /^cal/i.test(k)){ sum += keyBytes(k); }
      }
    }catch(e){}
    return sum;
  }
  function countAllMarks(){
    var n = 0;
    for(var i=0;i<calendars.length;i++){
      var c = calendars[i];
      n += Object.keys(c.dateMarks || {}).length;
      var tk = Object.keys(c.timeMarks || {});
      for(var j=0;j<tk.length;j++){ n += ((c.timeMarks[tk[j]]) || []).length; }
    }
    return n;
  }

  function storageRow(label, sub, bytes, legacy){
    return '<div class="storage-row' + (legacy ? ' legacy' : '') + '">'
      + '<span class="storage-row-label">' + escapeHtml(label) + '</span>'
      + '<span class="storage-row-sub">' + escapeHtml(sub) + '</span>'
      + '<span class="storage-row-size">' + fmtSize(bytes) + '</span>'
      + '</div>';
  }

  function renderStorageInfo(){
    var box = document.getElementById('storageRows');
    if(!box) return;

    var calBytes = keysBytes(['calCalendars', 'calActiveCalendarId']);
    var imgBytes = keyBytes('calLocalImages');
    var folderBytes = keyBytes('calFolderImages');
    var cfgBytes = keysBytes(['calExpandMode', 'calGlass', 'calStepPresets', 'calOptionPresets', 'calBackgrounds']);
    var legacyBytes = keysBytes(['calMarkers', 'calDateMarks', 'calTimeMarks', 'calDateMarkValues']);
    var total = totalAppBytes();
    var limit = 5 * 1024 * 1024;                    /* 浏览器一般给 localStorage 约 5MB */
    var pct = Math.max(0, Math.min(100, Math.round(total / limit * 1000) / 10));

    var html = '';
    html += storageRow('日历数据', calendars.length + ' 个日历 / 约 ' + countAllMarks() + ' 条标记', calBytes);
    html += storageRow('导入的图片', localImages.length + ' 张（存在浏览器里，最占空间）', imgBytes);
    html += storageRow('文件夹图片清单', folderImageNames.length + ' 个文件名（图片本身不占空间）', folderBytes);
    html += storageRow('其他设置', '展开方式 / 跨度 / 选项预设 / 背景设置', cfgBytes);
    if(legacyBytes > 0){ html += storageRow('旧版本遗留数据', '已被新数据取代，可安全清除', legacyBytes, true); }
    html += '<div class="storage-total">合计约 <b>' + fmtSize(total) + '</b>　（浏览器上限约 5 MB，已用 ' + pct + '%）</div>';
    html += '<div class="storage-bar"><span style="width:' + pct + '%"></span></div>';
    box.innerHTML = html;
  }

  function clearActiveCalendarMarks(){
    var cal = findCalendar(activeCalendarId);
    if(!cal) return;
    if(Object.keys(dateMarks).length === 0 && Object.keys(timeMarks).length === 0 && Object.keys(dateMarkValues).length === 0){
      alert('日历「' + cal.name + '」目前没有任何标记。');
      return;
    }
    if(!confirm('确定清空日历「' + cal.name + '」的全部标记吗？\n日期标记、时间段标记与保存的数值都会被清除（标记色会保留），且无法恢复。')) return;
    dateMarks = {};
    timeMarks = {};
    dateMarkValues = {};
    cal.dateMarks = dateMarks;
    cal.timeMarks = timeMarks;
    cal.dateMarkValues = dateMarkValues;
    resetTransientState();
    renderAll();
    save();
    renderStorageInfo();
  }

  function clearAllAppData(){
    if(!confirm('确定清空全部数据吗？\n所有日历、标记色、日期标记、时间段标记、数值、背景设置与已导入的图片都会被删除，且无法恢复。')) return;
    if(!confirm('再次确认：此操作不可撤销，确定要继续吗？')) return;
    try{
      var keys = [];
      for(var i=0;i<localStorage.length;i++){ keys.push(localStorage.key(i)); }
      for(var j=0;j<keys.length;j++){
        if(keys[j] && /^cal/i.test(keys[j])){ localStorage.removeItem(keys[j]); }
      }
    }catch(e){}
    try{ location.reload(); }catch(e){}
  }

  /* ---------- 液态玻璃 ---------- */
  function applyGlass(){
    var on = !!state.glass;
    if(on){ document.body.classList.add('liquid'); }
    else { document.body.classList.remove('liquid'); }
    var cb = document.getElementById('glassToggle');
    if(cb){ cb.checked = on; }
    lockBgSliders(on);
    var hint = document.getElementById('glassLockHint');
    if(hint){ hint.style.display = on ? 'block' : 'none'; }
  }

  /* 液态玻璃开启时，背景的透明度 / 模糊度 / 模块不透明度不可调节 */
  function lockBgSliders(locked){
    var ids = ['bgOpacity', 'bgOpacityNum', 'bgBlur', 'bgBlurNum', 'bgPanel', 'bgPanelNum'];
    for(var i=0;i<ids.length;i++){
      var el = document.getElementById(ids[i]);
      if(!el) continue;
      el.disabled = !!locked;
      var row = qclosest(el, '.bg-slider-row');
      if(row){
        if(locked){ row.classList.add('locked'); } else { row.classList.remove('locked'); }
      }
    }
  }

  function setGlass(on){
    state.glass = !!on;
    applyGlass();
    save();
  }

  /* ---------- 设置左侧导航 ---------- */
  function setActiveNav(id){
    var items = document.querySelectorAll('#settingsNav .settings-nav-item');
    for(var i=0;i<items.length;i++){
      if(items[i].getAttribute('data-target') === id){ items[i].classList.add('active'); }
      else { items[i].classList.remove('active'); }
    }
  }

  function scrollSettingsTo(id){
    var body = document.getElementById('settingsBody');
    var sec = document.getElementById(id);
    if(!body || !sec) return;
    var delta = sec.getBoundingClientRect().top - body.getBoundingClientRect().top;
    var top = Math.max(0, body.scrollTop + delta - 8);
    try{
      if(body.scrollTo){ body.scrollTo({ top: top, behavior: 'smooth' }); }
      else { body.scrollTop = top; }
    }catch(e){ body.scrollTop = top; }
  }

  function bindSettingsNav(){
    var nav = document.getElementById('settingsNav');
    var body = document.getElementById('settingsBody');
    if(!nav || !body) return;
    nav.addEventListener('click', function(e){
      var item = qclosest(e.target, '.settings-nav-item');
      if(!item) return;
      var id = item.getAttribute('data-target');
      if(!id) return;
      setActiveNav(id);
      scrollSettingsTo(id);
    });
    body.addEventListener('scroll', function(){
      var secs = document.querySelectorAll('#settingsBody .settings-group');
      if(!secs.length) return;
      var bodyTop = body.getBoundingClientRect().top;
      var cur = secs[0].id;
      for(var i=0;i<secs.length;i++){
        if((secs[i].getBoundingClientRect().top - bodyTop) <= 28){ cur = secs[i].id; }
      }
      setActiveNav(cur);
    });
  }

  /* ---------- AI 窗口 ---------- */
  function openAi(){ document.getElementById('aiOverlay').classList.add('show'); }
  function closeAi(){ document.getElementById('aiOverlay').classList.remove('show'); }

  /* ---------- 设置界面 ---------- */
  function renderSettings(){
    renderStorageInfo();
    renderCalSettings();
    renderBgSettings();
    applyBackground();
    applyGlass();
    var mbs = document.querySelectorAll('.mode-btn');
    for(var mb=0;mb<mbs.length;mb++){
      if(mbs[mb].getAttribute('data-mode') === state.expandMode){ mbs[mb].classList.add('active'); }
      else { mbs[mb].classList.remove('active'); }
    }
    var stepEl = document.getElementById('settingsStepPresets');
    var sh = '';
    for(var i=0;i<stepPresets.length;i++){
      sh += '<span class="step-preset' + (stepPresets[i]===state.stepSize?' active':'') + '" data-step="' + stepPresets[i] + '">'
        + stepPresets[i] + '分'
        + '<button class="step-preset-del" data-step="' + stepPresets[i] + '" title="删除">&#10005;</button>'
        + '</span>';
    }
    stepEl.innerHTML = sh;
    bindSettingsStepEvents();

    var optEl = document.getElementById('settingsOptionPresets');
    var oh = '';
    for(var c=2;c<=7;c++){
      var ps = optionPresets[String(c)] || [];
      for(var p=0;p<ps.length;p++){
        oh += '<div class="option-preset" data-count="' + c + '" data-idx="' + p + '">'
          + '<span class="option-preset-count">' + c + '项</span>'
          + '<span class="option-preset-labels">' + escapeHtml(ps[p].join('/')) + '</span>'
          + '<button class="option-preset-del" data-count="' + c + '" data-idx="' + p + '" title="删除">&#10005;</button>'
          + '</div>';
      }
    }
    if(oh === ''){ oh = '<div class="empty-hint">暂无预设</div>'; }
    optEl.innerHTML = oh;
    bindSettingsOptionEvents();
  }

  function bindSettingsStepEvents(){
    var el = document.getElementById('settingsStepPresets');
    var presets = el.querySelectorAll('.step-preset');
    for(var i=0;i<presets.length;i++){
      (function(p){
        p.addEventListener('click', function(e){
          if(qclosest(e.target, '.step-preset-del')) return;
          state.stepSize = parseInt(p.getAttribute('data-step'), 10);
          document.getElementById('stepCustom').value = '';
          highlightStep();
          renderSettings();
        });
        var del = p.querySelector('.step-preset-del');
        if(del){
          del.addEventListener('click', function(){
            var s = parseInt(p.getAttribute('data-step'), 10);
            stepPresets = stepPresets.filter(function(x){ return x !== s; });
            renderSettings();
            renderStepOptions();
            save();
          });
        }
      })(presets[i]);
    }
  }

  function bindSettingsOptionEvents(){
    var el = document.getElementById('settingsOptionPresets');
    var presets = el.querySelectorAll('.option-preset');
    for(var i=0;i<presets.length;i++){
      (function(p){
        var del = p.querySelector('.option-preset-del');
        if(del){
          del.addEventListener('click', function(){
            var c = parseInt(p.getAttribute('data-count'), 10);
            var idx = parseInt(p.getAttribute('data-idx'), 10);
            optionPresets[String(c)].splice(idx, 1);
            renderSettings();
            save();
          });
        }
      })(presets[i]);
    }
  }

  /* ---------- 时间跨度面板 ---------- */
  function highlightStep(){
    var opts = document.querySelectorAll('#stepOptions .step-opt');
    for(var i=0;i<opts.length;i++){
      if(parseInt(opts[i].getAttribute('data-step'),10) === state.stepSize){
        opts[i].classList.add('active');
      } else {
        opts[i].classList.remove('active');
      }
    }
  }

  function renderStepOptions(){
    var el = document.getElementById('stepOptions');
    var html = '';
    for(var i=0;i<stepPresets.length;i++){
      html += '<button class="step-opt' + (stepPresets[i]===state.stepSize?' active':'') + '" data-step="' + stepPresets[i] + '">' + stepPresets[i] + '分</button>';
    }
    el.innerHTML = html;
  }

  function bindStepPanel(){
    document.getElementById('stepOptions').addEventListener('click', function(e){
      var b = qclosest(e.target, '.step-opt');
      if(b){
        state.stepSize = parseInt(b.getAttribute('data-step'), 10);
        document.getElementById('stepCustom').value = '';
        highlightStep();
      }
    });
    document.getElementById('stepCustom').addEventListener('input', function(e){
      var v = parseInt(e.target.value, 10);
      if(!isNaN(v) && v > 0){
        state.stepSize = v;
        highlightStep();
      }
    });
  }

  /* ---------- 背景图片 ---------- */
  var IMG_RE = /\.(png|jpe?g|gif|webp|bmp|avif|svg)$/i;

  var DEFAULT_PANEL_ALPHA = 86;

  function bgNum(v, def){
    return (typeof v === 'number' && isFinite(v)) ? clamp(Math.round(v), 0, 100) : def;
  }

  function sanitizeBg(o){
    o = o || {};
    /* 兼容旧版本：以前整页展开 / 长页面展开各有一套背景，现在合并成一套 */
    if(o.page || o.long){
      var a = o.page || {}, b = o.long || {};
      var pick = a.imageId ? a : (b.imageId ? b : a);
      o = { imageId: pick.imageId, opacity: pick.opacity, blur: pick.blur, panelAlpha: o.panelAlpha };
    }
    return {
      imageId: (typeof o.imageId === 'string' && o.imageId !== '') ? o.imageId : null,
      opacity: bgNum(o.opacity, 100),
      blur: bgNum(o.blur, 0),
      panelAlpha: bgNum(o.panelAlpha, DEFAULT_PANEL_ALPHA)
    };
  }

  /* 全页共用一套背景（整页展开 / 长页面展开不再分开） */
  function bgConfig(){
    backgrounds = sanitizeBg(backgrounds);
    return backgrounds;
  }

  function isImageName(n){ return IMG_RE.test(String(n || '')); }
  function isImageFile(f){
    if(!f) return false;
    if(f.type && /^image\//i.test(f.type)) return true;
    return isImageName(f.name);
  }
  function encodePath(p){ return String(p).split('/').map(function(s){ return encodeURIComponent(s); }).join('/'); }
  function cssUrl(u){ return 'url(' + JSON.stringify(String(u)) + ')'; }

  function allImages(){
    var out = [];
    for(var i=0;i<folderImageNames.length;i++){
      var n = folderImageNames[i];
      if(hiddenImages.indexOf(n) !== -1) continue;
      out.push({ id:'f:' + n, name:n, kind:'folder', src:'image/' + encodePath(n) });
    }
    for(var j=0;j<localImages.length;j++){
      var li = localImages[j];
      if(li && li.id && li.src){ out.push({ id:li.id, name:li.name || '已导入图片', kind:'local', src:li.src }); }
    }
    return out;
  }

  function findImage(id){
    if(!id) return null;
    var all = allImages();
    for(var i=0;i<all.length;i++){ if(all[i].id === id) return all[i]; }
    return null;
  }

  function applyBackground(){
    var layer = document.getElementById('bgImage');
    var cfg = bgConfig();
    /* 模块不透明度：日历、标记色、Shift 框选跨度等所有模块统一使用这一个值 */
    document.body.style.setProperty('--mod-alpha', String(cfg.panelAlpha / 100));
    if(!layer) return;
    var img = findImage(cfg.imageId);
    if(!img){
      document.body.classList.remove('has-bg');
      layer.style.backgroundImage = 'none';
      return;
    }
    document.body.classList.add('has-bg');
    layer.style.backgroundImage = cssUrl(img.src);
    layer.style.opacity = String(cfg.opacity / 100);
    layer.style.filter = (cfg.blur > 0) ? ('blur(' + cfg.blur + 'px)') : 'none';
    layer.style.transform = 'scale(' + (1 + cfg.blur / 180) + ')';
  }

  function saveBackgrounds(){
    try{
      localStorage.setItem('calBackgrounds', JSON.stringify(backgrounds));
      localStorage.setItem('calFolderImages', JSON.stringify(folderImageNames));
      localStorage.setItem('calHiddenImages', JSON.stringify(hiddenImages));
      localStorage.setItem('calLocalImages', JSON.stringify(localImages));
      clearSaveWarning();
      return true;
    }catch(e){
      notifySaveFailed();
      return false;
    }
  }

  /* 扫描（探测）image 文件夹里的图片：目录列表 / manifest.js / manifest.json 三种方式 */
  function probeDirListing(cb){
    try{
      fetch('image/', { cache:'no-store' }).then(function(res){
        if(!res || !res.ok) throw new Error('no listing');
        return res.text();
      }).then(function(text){
        var names = [];
        var re = /href\s*=\s*["']([^"']+)["']/gi, m;
        while((m = re.exec(text))){
          var href = m[1];
          if(/^([a-z]+:|\/\/|#|\?)/i.test(href)) continue;
          var segs = href.split('/').filter(function(s){ return s !== ''; });
          if(!segs.length) continue;
          var last = decodeURIComponent(segs[segs.length-1].split('?')[0]);
          if(isImageName(last) && names.indexOf(last) === -1) names.push(last);
        }
        cb(names);
      })['catch'](function(){ cb([]); });
    }catch(e){ cb([]); }
  }

  function probeManifestJs(cb){
    var done = false;
    var scriptEl = null;
    function finish(names){
      if(done) return;
      done = true;
      if(scriptEl && scriptEl.parentNode) scriptEl.parentNode.removeChild(scriptEl);
      cb(names || []);
    }
    try{
      scriptEl = document.createElement('script');
      var q = (location.protocol === 'http:' || location.protocol === 'https:') ? ('?t=' + Date.now()) : '';
      scriptEl.src = 'image/manifest.js' + q;
      scriptEl.async = true;
      scriptEl.onload = function(){
        var list = [];
        try{
          if(Object.prototype.toString.call(window.CAL_IMAGE_LIST) === '[object Array]'){ list = window.CAL_IMAGE_LIST.slice(); }
        }catch(e){}
        try{ window.CAL_IMAGE_LIST = []; }catch(e){}
        finish(list.map(function(x){ return String(x || ''); }).filter(isImageName));
      };
      scriptEl.onerror = function(){ finish([]); };
      document.head.appendChild(scriptEl);
      setTimeout(function(){ finish([]); }, 5000);
    }catch(e){ finish([]); }
  }

  function probeManifestJson(cb){
    try{
      fetch('image/manifest.json', { cache:'no-store' }).then(function(res){
        if(!res || !res.ok) throw new Error('no manifest');
        return res.json();
      }).then(function(data){
        var list = [];
        if(Object.prototype.toString.call(data) === '[object Array]'){ list = data; }
        else if(data && Object.prototype.toString.call(data.images) === '[object Array]'){ list = data.images; }
        cb(list.map(function(x){ return (typeof x === 'string') ? x : ((x && x.name) || ''); }).filter(isImageName));
      })['catch'](function(){ cb([]); });
    }catch(e){ cb([]); }
  }

  function mergeFolderNames(names){
    var changed = false;
    for(var i=0;i<names.length;i++){
      var n = String(names[i] || '').trim();
      if(!n || !isImageName(n)) continue;
      if(hiddenImages.indexOf(n) !== -1) continue;   /* 用户已从列表移除过，不再自动加回来 */
      if(folderImageNames.indexOf(n) === -1){ folderImageNames.push(n); changed = true; }
    }
    return changed;
  }

  function refreshImageList(onDone){
    var acc = [];
    var pending = 3;
    function one(names){
      for(var i=0;i<names.length;i++){ if(acc.indexOf(names[i]) === -1) acc.push(names[i]); }
      pending--;
      if(pending === 0){
        var changed = mergeFolderNames(acc);
        if(changed) saveBackgrounds();
        applyBackground();
        if(typeof onDone === 'function') onDone(acc.length);
      }
    }
    probeDirListing(one);
    probeManifestJs(one);
    probeManifestJson(one);
  }

  /* 前端导入：把文件读成 data URL（过大的图片先压缩），存在浏览器本地 */
  function readImageFile(file){
    return new Promise(function(resolve, reject){
      var reader = new FileReader();
      reader.onerror = function(){ reject(new Error('读取失败')); };
      reader.onload = function(){ resolve(String(reader.result || '')); };
      reader.readAsDataURL(file);
    }).then(function(dataUrl){
      if(!dataUrl || dataUrl.length <= 800 * 1024) return dataUrl;
      return new Promise(function(resolve){
        var img = new Image();
        img.onerror = function(){ resolve(dataUrl); };
        img.onload = function(){
          try{
            var w = img.width || 1, h = img.height || 1;
            var scale = Math.min(1, 1920 / Math.max(w, h));
            var cw = Math.max(1, Math.round(w * scale)), ch = Math.max(1, Math.round(h * scale));
            var cv = document.createElement('canvas');
            cv.width = cw; cv.height = ch;
            var ctx = cv.getContext ? cv.getContext('2d') : null;
            if(!ctx) return resolve(dataUrl);
            ctx.fillStyle = '#ffffff';
            ctx.fillRect(0, 0, cw, ch);
            ctx.drawImage(img, 0, 0, cw, ch);
            resolve(cv.toDataURL('image/jpeg', 0.85));
          }catch(e){ resolve(dataUrl); }
        };
        img.src = dataUrl;
      });
    });
  }

  /* 用「扫描文件夹」方式导入时，只记录文件名，直接引用 image 文件夹里的原图 */
  function folderRelativeName(f){
    var p = (f && (f.webkitRelativePath || f.name)) || '';
    if(!p) return '';
    var m = String(p).replace(/\\/g, '/').match(/(?:^|\/)image\/(.+)$/i);
    if(!m) return '';
    var rel = m[1];
    return isImageName(rel) ? rel : '';
  }

  function importImageFiles(files, fromFolder, onDone){
    var arr = [];
    for(var i=0;i<(files ? files.length : 0);i++){ if(isImageFile(files[i])) arr.push(files[i]); }
    if(arr.length === 0){
      alert('没有找到可用的图片文件（支持 png / jpg / jpeg / gif / webp / bmp / avif / svg）');
      if(onDone) onDone(0, 0);
      return;
    }
    var added = 0, failed = 0;

    if(fromFolder){
      for(var k=0;k<arr.length;k++){
        var rel = folderRelativeName(arr[k]);
        if(!rel){ failed++; continue; }
        var hi = hiddenImages.indexOf(rel);
        if(hi !== -1){ hiddenImages.splice(hi, 1); }   /* 用户主动扫描回来了，取消隐藏 */
        if(folderImageNames.indexOf(rel) === -1){ folderImageNames.push(rel); added++; }
      }
      if(added) saveBackgrounds();
      renderBgSettings();
      applyBackground();
      if(onDone) onDone(added, failed);
      return;
    }

    var idx = 0;
    function next(){
      if(idx >= arr.length){ finish(); return; }
      var f = arr[idx];
      idx++;
      readImageFile(f).then(function(dataUrl){
        if(dataUrl){
          localImages.push({ id:'l' + Date.now().toString(36) + '_' + idx, name:f.name, src:dataUrl });
          added++;
        } else { failed++; }
        next();
      })['catch'](function(){ failed++; next(); });
    }
    function finish(){
      var ok = true;
      if(added){ ok = saveBackgrounds(); }
      if(!ok){
        localImages = [];
        saveBackgrounds();
        alert('图片过大，浏览器本地存储空间不足，本次导入没有保存。可以把图片放进 image 文件夹后使用「扫描 image 文件夹」。');
      }
      renderBgSettings();
      if(onDone) onDone(added, failed);
    }
    next();
  }

  /* 把一张「文件夹图片」从列表里移除：只移除记录，不动 image 文件夹里的文件，
     并记进 hiddenImages，刷新/自动探测不会再把它扫回来。 */
  function removeFolderImage(name){
    if(!name) return;
    if(!confirm('从背景列表里移除「' + name + '」吗？\n只从列表中移除，image 文件夹里的文件不会被删除。\n以后想再用它，可以重新点「扫描 image 文件夹」。')) return;
    folderImageNames = folderImageNames.filter(function(n){ return n !== name; });
    if(hiddenImages.indexOf(name) === -1){ hiddenImages.push(name); }
    if(bgConfig().imageId === 'f:' + name){ backgrounds.imageId = null; }
    saveBackgrounds();
    applyBackground();
    renderBgSettings();
  }

  function removeLocalImage(id){
    var img = null;
    for(var i=0;i<localImages.length;i++){ if(localImages[i].id === id) img = localImages[i]; }
    if(!img) return;
    if(!confirm('删除已导入的图片「' + img.name + '」吗？（image 文件夹里的原图不受影响）')) return;
    localImages = localImages.filter(function(x){ return x.id !== id; });
    if(bgConfig().imageId === id){ backgrounds.imageId = null; }
    saveBackgrounds();
    applyBackground();
    renderBgSettings();
  }

  var BG_FIELDS = {
    opacity: ['bgOpacity', 'bgOpacityNum'],
    blur: ['bgBlur', 'bgBlurNum'],
    panelAlpha: ['bgPanel', 'bgPanelNum']
  };

  function setBgValue(key, v, persist){
    v = clamp(parseInt(v, 10) || 0, 0, 100);
    bgConfig()[key] = v;
    var ids = BG_FIELDS[key] || [];
    var r = document.getElementById(ids[0]);
    var n = document.getElementById(ids[1]);
    if(r) r.value = v;
    if(n) n.value = v;
    applyBackground();
    if(persist) saveBackgrounds();
  }

  function renderBgSettings(){
    var grid = document.getElementById('bgGrid');
    if(!grid) return;
    var cfg = bgConfig();
    var images = allImages();
    var html = '<button type="button" class="bg-item bg-none' + (!cfg.imageId ? ' active' : '') + '" data-id="" title="不使用背景图片">无背景</button>';
    for(var i=0;i<images.length;i++){
      var im = images[i];
      html += '<button type="button" class="bg-item' + (cfg.imageId === im.id ? ' active' : '') + '" data-id="' + escapeAttr(im.id) + '" title="' + escapeAttr(im.name) + '">'
        + '<img class="bg-thumb" data-src="' + escapeAttr(im.src) + '" alt="">'
        + '<span class="bg-missing">文件不存在</span>'
        + '<span class="bg-name">' + escapeHtml(im.name) + '</span>'
        + '<span class="bg-del" data-del="' + escapeAttr(im.id) + '" title="'
        + (im.kind === 'local' ? '删除这张已导入的图片' : '从列表中移除（不删除 image 文件夹里的文件）') + '">&#10005;</span>'
        + '</button>';
    }
    if(images.length === 0){
      html += '<div class="bg-empty">image 文件夹里还没有图片，也没有导入过图片</div>';
    }
    grid.innerHTML = html;

    /* 缩略图逐个绑定后再赋 src：这样能准确捕获「文件不存在」的情况 */
    missingImages = {};
    var thumbs = grid.querySelectorAll('.bg-thumb');
    for(var t=0;t<thumbs.length;t++){
      (function(img){
        var item = qclosest(img, '.bg-item');
        var id = item ? (item.getAttribute('data-id') || '') : '';
        img.addEventListener('error', function(){
          if(item) item.classList.add('missing');
          if(id){ missingImages[id] = true; }
          updateMissingImages();
        });
        img.addEventListener('load', function(){
          if(item) item.classList.remove('missing');
          if(id){ delete missingImages[id]; }
          updateMissingImages();
        });
        var s = img.getAttribute('data-src') || '';
        if(s){ img.src = s; } else { img.dispatchEvent(new Event('error')); }
      })(thumbs[t]);
    }
    updateMissingImages();

    var fields = ['opacity', 'blur', 'panelAlpha'];
    for(var f=0; f<fields.length; f++){
      var ids = BG_FIELDS[fields[f]];
      var rEl = document.getElementById(ids[0]);
      var nEl = document.getElementById(ids[1]);
      if(rEl) rEl.value = cfg[fields[f]];
      if(nEl) nEl.value = cfg[fields[f]];
    }
  }

  function hasMissingImages(){
    for(var k in missingImages){ if(Object.prototype.hasOwnProperty.call(missingImages, k)) return true; }
    return false;
  }

  function updateMissingImages(){
    var btn = document.getElementById('bgCleanMissing');
    if(!btn) return;
    btn.style.display = hasMissingImages() ? 'inline-block' : 'none';
  }

  /* 一次性移除所有「文件已经不在了」的图片 */
  function removeMissingImages(){
    var ids = [];
    for(var k in missingImages){ if(Object.prototype.hasOwnProperty.call(missingImages, k)) ids.push(k); }
    if(ids.length === 0) return;
    if(!confirm('移除 ' + ids.length + ' 张已失效的图片吗？（image 文件夹里已经没有这些文件了；只影响列表）')) return;
    for(var i=0;i<ids.length;i++){
      var id = ids[i];
      if(id.indexOf('f:') === 0){
        var name = id.slice(2);
        folderImageNames = folderImageNames.filter(function(n){ return n !== name; });
        if(hiddenImages.indexOf(name) === -1){ hiddenImages.push(name); }
      } else {
        localImages = localImages.filter(function(x){ return x.id !== id; });
      }
      if(bgConfig().imageId === id){ backgrounds.imageId = null; }
    }
    missingImages = {};
    saveBackgrounds();
    applyBackground();
    renderBgSettings();
  }

  function bindBgEvents(){
    var grid = document.getElementById('bgGrid');
    if(grid){
      grid.addEventListener('click', function(e){
        var del = qclosest(e.target, '.bg-del');
        if(del){
          var delId = del.getAttribute('data-del') || '';
          if(delId.indexOf('f:') === 0){ removeFolderImage(delId.slice(2)); }
          else { removeLocalImage(delId); }
          return;
        }
        var item = qclosest(e.target, '.bg-item');
        if(!item) return;
        var id = item.getAttribute('data-id');
        bgConfig().imageId = (id ? id : null);
        applyBackground();
        saveBackgrounds();
        renderBgSettings();
      });
    }
    var impBtn = document.getElementById('bgImportBtn');
    var impInput = document.getElementById('bgFileInput');
    if(impBtn && impInput){ impBtn.addEventListener('click', function(){ impInput.click(); }); }
    var scanBtn = document.getElementById('bgScanBtn');
    var dirInput = document.getElementById('bgDirInput');
    if(scanBtn && dirInput){ scanBtn.addEventListener('click', function(){ dirInput.click(); }); }
    if(impInput){
      impInput.addEventListener('change', function(){
        importImageFiles(impInput.files, false, function(added){
          impInput.value = '';
          if(!added){ alert('没有导入任何图片'); }
        });
      });
    }
    if(dirInput){
      dirInput.addEventListener('change', function(){
        importImageFiles(dirInput.files, true, function(added){
          dirInput.value = '';
          if(!added){ alert('没有识别到 image 文件夹中的图片，请在文件选择窗口里选择本项目目录下的 image 文件夹。'); }
        });
      });
    }
    var cleanBtn = document.getElementById('bgCleanMissing');
    if(cleanBtn){ cleanBtn.addEventListener('click', removeMissingImages); }
    var refBtn = document.getElementById('bgRefreshBtn');
    if(refBtn){
      refBtn.addEventListener('click', function(){
        refBtn.disabled = true;
        refBtn.textContent = '检测中…';
        refreshImageList(function(){
          refBtn.disabled = false;
          refBtn.textContent = '刷新图片列表';
          renderBgSettings();
        });
      });
    }
    var fields = ['opacity', 'blur', 'panelAlpha'];
    for(var i=0;i<fields.length;i++){
      (function(key){
        var ids = BG_FIELDS[key];
        var r = document.getElementById(ids[0]), n = document.getElementById(ids[1]);
        if(!r || !n) return;
        r.addEventListener('input', function(){ setBgValue(key, r.value, false); });
        r.addEventListener('change', function(){ setBgValue(key, r.value, true); });
        n.addEventListener('input', function(){ if(n.value === '') return; setBgValue(key, n.value, false); });
        n.addEventListener('change', function(){ setBgValue(key, n.value, true); });
      })(fields[i]);
    }
  }

  /* ---------- 多日历管理 ---------- */
  var CN_NUM = ['一','二','三','四','五','六','七','八','九','十','十一','十二','十三','十四','十五','十六','十七','十八','十九','二十'];

  function newCalendarId(){
    calIdCounter++;
    return 'cal' + Date.now().toString(36) + '_' + calIdCounter;
  }

  function findCalendar(id){
    for(var i=0;i<calendars.length;i++){ if(calendars[i].id === id) return calendars[i]; }
    return null;
  }

  function calendarNameExists(name, exceptId){
    for(var i=0;i<calendars.length;i++){
      if(calendars[i].name === name && calendars[i].id !== exceptId) return true;
    }
    return false;
  }

  function defaultCalendarName(){
    for(var n=1;n<=999;n++){
      var nm = '日历' + (n<=CN_NUM.length ? CN_NUM[n-1] : n);
      if(!calendarNameExists(nm, null)) return nm;
    }
    return '新日历';
  }

  function isPlainObject(o){ return !!o && typeof o === 'object' && !Array.isArray(o); }

  function normalizeCalendar(src, fallbackName){
    src = src || {};
    var cal = {
      id: (typeof src.id === 'string' && src.id !== '') ? src.id : newCalendarId(),
      name: (typeof src.name === 'string' && src.name.trim() !== '') ? src.name.trim().slice(0,20) : (fallbackName || '日历'),
      markers: Array.isArray(src.markers) ? src.markers.filter(function(m){ return m && typeof m === 'object'; }) : [],
      dateMarks: isPlainObject(src.dateMarks) ? src.dateMarks : {},
      timeMarks: isPlainObject(src.timeMarks) ? src.timeMarks : {},
      dateMarkValues: isPlainObject(src.dateMarkValues) ? src.dateMarkValues : {},
      markerIdCounter: 0
    };
    var maxId = 0;
    for(var i=0;i<cal.markers.length;i++){
      if(typeof cal.markers[i].id !== 'number') cal.markers[i].id = i + 1;
      if(cal.markers[i].id > maxId) maxId = cal.markers[i].id;
    }
    var saved = (typeof src.markerIdCounter === 'number' && src.markerIdCounter > 0) ? src.markerIdCounter : 0;
    cal.markerIdCounter = Math.max(saved, maxId);
    return cal;
  }

  function newEmptyCalendar(name){
    return { id:newCalendarId(), name:name, markers:[], dateMarks:{}, timeMarks:{}, dateMarkValues:{}, markerIdCounter:0 };
  }

  /* 把当前实时数据写回所属日历对象 */
  function commitActiveCalendar(){
    var cal = findCalendar(activeCalendarId);
    if(!cal) return;
    cal.markers = markers;
    cal.dateMarks = dateMarks;
    cal.timeMarks = timeMarks;
    cal.dateMarkValues = dateMarkValues;
    cal.markerIdCounter = markerIdCounter;
  }

  /* 把指定日历的数据绑定为当前实时数据 */
  function bindActiveCalendar(){
    var cal = findCalendar(activeCalendarId) || calendars[0];
    if(!cal) return;
    activeCalendarId = cal.id;
    markers = cal.markers;
    dateMarks = cal.dateMarks;
    timeMarks = cal.timeMarks;
    dateMarkValues = cal.dateMarkValues;
    markerIdCounter = cal.markerIdCounter || 0;
  }

  function resetTransientState(){
    cancelPressHold();
    markDrag.active = false;
    markDrag.markId = null;
    markDrag.pressPending = false;
    dateDrag.active = false;
    dateDrag.anchor = null;
    dateDrag.lastKey = null;
    detailDrag.active = false;
    detailDrag.col = null;
    document.body.classList.remove('mark-moving');
    state.selectedDates = new Set();
    state.anchorDate = null;
    state.selectedMarkerId = null;
    state.selectedTimeMarkId = null;
    state.pendingTime = null;
    state.expandedWeekIndex = null;
    state.detailJustExpanded = false;
    closeValueEditor();
    hideTooltip();
  }

  function switchCalendar(id){
    if(!id || id === activeCalendarId) return;
    if(!findCalendar(id)) return;
    commitActiveCalendar();
    activeCalendarId = id;
    bindActiveCalendar();
    resetTransientState();
    renderAll();
    save();
  }

  function addCalendar(rawName){
    var name = (typeof rawName === 'string') ? rawName.trim() : '';
    if(name === '') name = defaultCalendarName();
    if(name.length > 20) name = name.slice(0,20);
    if(calendarNameExists(name, null)){ alert('已存在名为「' + name + '」的日历，请换一个名称。'); return null; }
    var cal = newEmptyCalendar(name);
    calendars.push(cal);
    switchCalendar(cal.id);
    return cal;
  }

  function deleteCalendar(id){
    var cal = findCalendar(id);
    if(!cal) return;
    if(calendars.length <= 1){ alert('至少需要保留一个日历，无法删除。'); return; }
    if(!confirm('确定要删除日历「' + cal.name + '」吗？\n该日历中的全部标记与数值都会一并删除，且无法恢复。')) return;
    var wasActive = (id === activeCalendarId);
    renamingCalId = null;
    calendars = calendars.filter(function(c){ return c.id !== id; });
    if(wasActive){
      activeCalendarId = calendars[0].id;
      bindActiveCalendar();
      resetTransientState();
      renderAll();
    } else {
      renderCalSwitcher();
    }
    renderCalSettings();
    save();
  }

  function startRenameCal(id){
    if(!findCalendar(id)) return;
    renamingCalId = id;
    renderCalSettings();
  }

  function commitRenameCal(id, raw){
    renamingCalId = null;
    var cal = findCalendar(id);
    if(!cal){ renderCalSettings(); return; }
    var name = (typeof raw === 'string') ? raw.trim() : '';
    if(name === ''){ renderCalSettings(); return; }
    if(name.length > 20) name = name.slice(0,20);
    if(name !== cal.name && calendarNameExists(name, id)){
      alert('已存在名为「' + name + '」的日历，请换一个名称。');
      renderCalSettings();
      return;
    }
    cal.name = name;
    renderCalSettings();
    renderCalSwitcher();
    save();
  }

  function renderCalSwitcher(){
    var cal = findCalendar(activeCalendarId);
    var nameEl = document.getElementById('calSwitchName');
    var btn = document.getElementById('calSwitchBtn');
    if(nameEl) nameEl.textContent = cal ? cal.name : '日历';
    if(btn) btn.title = '当前日历：' + (cal ? cal.name : '') + '（点击切换 / 管理）';
    var menu = document.getElementById('calMenu');
    if(!menu) return;
    var html = '';
    for(var i=0;i<calendars.length;i++){
      var c = calendars[i];
      var isAct = (c.id === activeCalendarId);
      html += '<button class="cal-menu-item' + (isAct?' active':'') + '" data-id="' + escapeAttr(c.id) + '" title="' + escapeAttr(c.name) + '">'
        + '<span class="cal-menu-check">' + (isAct ? '&#10003;' : '') + '</span>'
        + '<span class="cal-menu-name">' + escapeHtml(c.name) + '</span>'
        + '</button>';
    }
    html += '<div class="cal-menu-sep"></div>'
      + '<button class="cal-menu-item" data-manage="1">'
      + '<span class="cal-menu-check">&#9881;</span>'
      + '<span class="cal-menu-name">管理日历…</span>'
      + '</button>';
    menu.innerHTML = html;
  }

  function renderCalSettings(){
    var el = document.getElementById('calManageList');
    if(!el) return;
    var html = '';
    for(var i=0;i<calendars.length;i++){
      var c = calendars[i];
      var isAct = (c.id === activeCalendarId);
      html += '<div class="cal-manage-item' + (isAct?' active':'') + '" data-id="' + escapeAttr(c.id) + '">'
        + '<span class="cal-manage-dot"></span>';
      if(renamingCalId === c.id){
        html += '<input type="text" class="cal-manage-name-input" maxlength="20" value="' + escapeAttr(c.name) + '">';
      } else {
        html += '<span class="cal-manage-name" title="' + escapeAttr(c.name) + '">' + escapeHtml(c.name) + '</span>';
        if(isAct) html += '<span class="cal-manage-badge">使用中</span>';
      }
      html += '<button class="cal-manage-btn" data-act="rename" title="重命名">&#9998;</button>'
        + '<button class="cal-manage-btn del" data-act="del" title="删除日历">&#10005;</button>'
        + '</div>';
    }
    el.innerHTML = html;
    bindCalSettingsEvents();
    if(renamingCalId !== null){
      var inp = el.querySelector('.cal-manage-name-input');
      if(inp){ inp.focus(); inp.select(); }
    }
  }

  function bindCalSettingsEvents(){
    var el = document.getElementById('calManageList');
    if(!el) return;
    var items = el.querySelectorAll('.cal-manage-item');
    for(var i=0;i<items.length;i++){
      (function(item){
        var id = item.getAttribute('data-id');
        item.addEventListener('click', function(e){
          if(qclosest(e.target, '.cal-manage-btn')) return;
          if(renamingCalId === id) return;
          if(id !== activeCalendarId) switchCalendar(id);
          renderSettings();
        });
        var rb = item.querySelector('[data-act="rename"]');
        if(rb){
          rb.addEventListener('click', function(e){
            e.stopPropagation();
            startRenameCal(id);
          });
        }
        var db = item.querySelector('[data-act="del"]');
        if(db){
          db.addEventListener('click', function(e){
            e.stopPropagation();
            deleteCalendar(id);
          });
        }
        var inp = item.querySelector('.cal-manage-name-input');
        if(inp){
          inp.addEventListener('click', function(e){ e.stopPropagation(); });
          inp.addEventListener('mousedown', function(e){ e.stopPropagation(); });
          inp.addEventListener('keydown', function(e){
            if(e.key === 'Enter'){ e.preventDefault(); commitRenameCal(id, inp.value); }
            else if(e.key === 'Escape'){ e.preventDefault(); renamingCalId = null; renderCalSettings(); }
          });
          inp.addEventListener('blur', function(){
            if(renamingCalId === id) commitRenameCal(id, inp.value);
          });
        }
      })(items[i]);
    }
  }

  function closeCalMenu(){
    var menu = document.getElementById('calMenu');
    if(menu) menu.classList.remove('show');
  }

  function bindCalSwitcher(){
    var sw = document.getElementById('calSwitch');
    var btn = document.getElementById('calSwitchBtn');
    var menu = document.getElementById('calMenu');
    if(!sw || !btn || !menu) return;
    btn.addEventListener('click', function(e){
      e.stopPropagation();
      menu.classList.toggle('show');
    });
    menu.addEventListener('click', function(e){
      var item = qclosest(e.target, '.cal-menu-item');
      if(!item) return;
      e.stopPropagation();
      if(item.getAttribute('data-manage')){
        closeCalMenu();
        openSettings();
        return;
      }
      var id = item.getAttribute('data-id');
      closeCalMenu();
      if(id !== activeCalendarId) switchCalendar(id);
    });
    document.addEventListener('click', function(e){
      if(!sw.contains(e.target)) closeCalMenu();
    });
  }

  function openSettings(){
    renderSettings();
    document.getElementById('settingsOverlay').classList.add('show');
    setActiveNav('sec-calendar');
    var body = document.getElementById('settingsBody');
    if(body){ body.scrollTop = 0; }
  }

  function closeSettings(){
    document.getElementById('settingsOverlay').classList.remove('show');
  }

  /* ---------- 持久化 ---------- */
  /* 旧版本（单日历）遗留的 4 个键：数据迁移到 calCalendars 之后就没有用了，
     这里主动清掉，避免同一份数据在浏览器里留两份、白占空间。 */
  function dropLegacyKeys(){
    try{
      if(!localStorage.getItem('calCalendars')) return;   /* 新数据没有写成功就不动旧数据 */
      var legacyKeys = ['calMarkers', 'calDateMarks', 'calTimeMarks', 'calDateMarkValues'];
      for(var i=0;i<legacyKeys.length;i++){
        if(localStorage.getItem(legacyKeys[i]) !== null){ localStorage.removeItem(legacyKeys[i]); }
      }
    }catch(e){}
  }

  var saveWarned = false;

  /* 存储空间不足时给出明确提示，而不是静默丢失修改 */
  function notifySaveFailed(){
    if(saveWarned) return;
    saveWarned = true;
    var el = document.getElementById('saveWarning');
    if(el) el.classList.add('show');
  }

  function clearSaveWarning(){
    if(!saveWarned) return;
    saveWarned = false;
    var el = document.getElementById('saveWarning');
    if(el) el.classList.remove('show');
  }

  function save(){
    commitActiveCalendar();
    try{
      localStorage.setItem('calCalendars', JSON.stringify(calendars));
      localStorage.setItem('calActiveCalendarId', activeCalendarId || '');
      localStorage.setItem('calExpandMode', state.expandMode);
      localStorage.setItem('calGlass', state.glass ? '1' : '0');
      localStorage.setItem('calStepPresets', JSON.stringify(stepPresets));
      localStorage.setItem('calOptionPresets', JSON.stringify(optionPresets));
      clearSaveWarning();
    }catch(e){
      notifySaveFailed();
    }
  }

  function load(){
    try{
      var em = localStorage.getItem('calExpandMode');
      if(em){ state.expandMode = em; }
      var gl = localStorage.getItem('calGlass');
      if(gl === '1'){ state.glass = true; } else if(gl === '0'){ state.glass = false; }
      var sp = localStorage.getItem('calStepPresets');
      if(sp){ stepPresets = JSON.parse(sp); }
      var op = localStorage.getItem('calOptionPresets');
      if(op){
        var savedOp = JSON.parse(op);
        for(var c=2;c<=7;c++){
          var sc = String(c);
          var cur = optionPresets[sc] || [];
          var savedArr = savedOp[sc] || [];
          for(var i=0;i<savedArr.length;i++){
            var key = savedArr[i].join('|');
            var exists = cur.some(function(x){ return x.join('|') === key; });
            if(!exists) cur.push(savedArr[i]);
          }
          optionPresets[sc] = cur;
        }
      }
      optionPresets['6'] = (optionPresets['6'] || []).filter(function(a){ return a.join('|') !== '很低|低|较低|较高|高|很高'; });
      optionPresets['7'] = (optionPresets['7'] || []).filter(function(a){ return a.join('|') !== '很低|低|较低|中|较高|高|很高'; });
    }catch(e){}

    /* --- 背景图片设置（旧版本分成 page / long 两套，这里会自动合并成一套） --- */
    var bgMigrated = false;
    try{
      var bgs = localStorage.getItem('calBackgrounds');
      if(bgs){
        var pb = JSON.parse(bgs);
        if(pb && typeof pb === 'object'){
          if(pb.page || pb.long || typeof pb.panelAlpha !== 'number'){ bgMigrated = true; }
          backgrounds = sanitizeBg(pb);
        }
      }
      var fn = localStorage.getItem('calFolderImages');
      if(fn){
        var fa = JSON.parse(fn);
        if(Object.prototype.toString.call(fa) === '[object Array]'){ folderImageNames = fa.filter(isImageName); }
      }
      var hid = localStorage.getItem('calHiddenImages');
      if(hid){
        var ha = JSON.parse(hid);
        if(Object.prototype.toString.call(ha) === '[object Array]'){
          hiddenImages = ha.map(function(x){ return String(x || ''); }).filter(function(x){ return x !== ''; });
        }
      }
      var li = localStorage.getItem('calLocalImages');
      if(li){
        var la = JSON.parse(li);
        if(Object.prototype.toString.call(la) === '[object Array]'){
          localImages = la.filter(function(x){ return x && x.id && x.src; });
        }
      }
    }catch(e){}
    if(bgMigrated){ saveBackgrounds(); }

    /* --- 日历数据：优先读取多日历存储，否则从旧版单日历存储迁移 --- */
    var stored = null;
    try{
      var raw = localStorage.getItem('calCalendars');
      if(raw){
        var parsed = JSON.parse(raw);
        if(parsed && parsed.length){ stored = parsed; }
      }
    }catch(e){ stored = null; }

    var isFresh = false;
    calendars = [];
    if(stored){
      for(var si=0; si<stored.length; si++){
        calendars.push(normalizeCalendar(stored[si], '日历' + (si+1)));
      }
    } else {
      var legacy = null;
      try{
        var lm = localStorage.getItem('calMarkers');
        var ldm = localStorage.getItem('calDateMarks');
        var ltm = localStorage.getItem('calTimeMarks');
        var ldv = localStorage.getItem('calDateMarkValues');
        if(lm !== null || ldm !== null || ltm !== null || ldv !== null){
          legacy = {
            markers: lm ? JSON.parse(lm) : [],
            dateMarks: ldm ? JSON.parse(ldm) : {},
            timeMarks: ltm ? JSON.parse(ltm) : {},
            dateMarkValues: ldv ? JSON.parse(ldv) : {}
          };
        }
      }catch(e){ legacy = null; }
      if(!legacy){ isFresh = true; }
      var first = normalizeCalendar({
        id: newCalendarId(),
        name: '日历一',
        markers: legacy ? legacy.markers : [],
        dateMarks: legacy ? legacy.dateMarks : {},
        timeMarks: legacy ? legacy.timeMarks : {},
        dateMarkValues: legacy ? legacy.dateMarkValues : {}
      }, '日历一');
      calendars.push(first);
    }
    if(calendars.length === 0){ calendars.push(newEmptyCalendar('日历一')); }

    var savedActive = null;
    try{ savedActive = localStorage.getItem('calActiveCalendarId'); }catch(e){}
    if(!savedActive || !findCalendar(savedActive)) savedActive = calendars[0].id;
    activeCalendarId = savedActive;
    bindActiveCalendar();

    if(isFresh){
      markers.push({ id: ++markerIdCounter, color: '#eab308', label: '运动' });
      markers.push({ id: ++markerIdCounter, color: '#06b6d4', label: '学习' });
    }
    commitActiveCalendar();
    save();
    dropLegacyKeys();
  }

  /* ---------- 事件绑定 ---------- */
  document.getElementById('prevBtn').addEventListener('click', function(){ changeMonth(-1, true); });
  document.getElementById('nextBtn').addEventListener('click', function(){ changeMonth(1, true); });
  document.getElementById('todayBtn').addEventListener('click', function(){
    var t = new Date();
    state.year = t.getFullYear();
    state.month = t.getMonth();
    state.selYear = t.getFullYear();
    state.expandedWeekIndex = null;
    state.pendingTime = null;
    var key = fmtDate(t);
    state.selectedDates = new Set([key]);
    state.anchorDate = key;
    renderAll();
  });

  var grid = document.getElementById('monthGrid');

  grid.addEventListener('pointerdown', function(e){
    var cell = qclosest(e.target, '.day-cell');
    if(cell && cell.getAttribute('data-date')){
      if(e.button !== 0) return;
      e.preventDefault();
      var key = cell.getAttribute('data-date');
      if(state.expandedWeekIndex !== null){
        state.expandedWeekIndex = null;
        state.pendingTime = null;
        renderMonth();
        updateToolbar();
      }
      beginDateDrag(key, e.shiftKey);
    }
  });

  grid.addEventListener('click', function(e){
    var exp = qclosest(e.target, '.expand-btn');
    if(exp){
      var wi = parseInt(exp.getAttribute('data-week'), 10);
      if(state.expandedWeekIndex === wi){
        collapseWeek();
      } else {
        state.expandedWeekIndex = wi;
        state.pendingTime = null;
        state.detailJustExpanded = true;
        renderMonth();
        updateToolbar();
      }
      return;
    }
    var head = qclosest(e.target, '.detail-day-head');
    if(head && head.getAttribute('data-date')){
      selectSingle(head.getAttribute('data-date'), e.shiftKey);
    }
  });

  grid.addEventListener('contextmenu', function(e){
    var tm = qclosest(e.target, '.time-mark');
    if(tm && tm.getAttribute('data-tmid')){
      e.preventDefault();
      openValueEditorForTime(tm.getAttribute('data-tmid'), e.clientX, e.clientY);
      return;
    }
    var dateEl = qclosest(e.target, '.day-cell') || qclosest(e.target, '.detail-day-head');
    if(dateEl && dateEl.getAttribute('data-date')){
      var key = dateEl.getAttribute('data-date');
      var ids = dateMarks[key] || [];
      if(ids.length > 0){
        e.preventDefault();
        openValueEditorForDate(key, ids, e.clientX, e.clientY);
      }
    }
  });

  document.addEventListener('pointermove', function(e){
    if(markDrag.pressPending){
      var pdx = e.clientX - markDrag.pressX;
      var pdy = e.clientY - markDrag.pressY;
      if(Math.sqrt(pdx*pdx + pdy*pdy) > 10) cancelPressHold();
    }
    if(markDrag.active){ updateMarkDrag(e); return; }
    if(!dateDrag.active) return;
    var el = document.elementFromPoint(e.clientX, e.clientY);
    var cell = qclosest(el, '.day-cell');
    if(cell && cell.getAttribute('data-date')){
      moveDateDrag(cell.getAttribute('data-date'));
    }
  });

  document.addEventListener('pointerup', function(e){
    if(markDrag.pressPending) cancelPressHold();
    if(markDrag.active) endMarkDrag();
    if(dateDrag.active) endDateDrag();
  });

  document.getElementById('yearCapsule').addEventListener('wheel', function(e){
    e.preventDefault();
    var dir = e.deltaY > 0 ? 1 : -1;
    state.selYear += dir;
    var el = document.getElementById('yearText');
    el.textContent = state.selYear + '年';
    el.classList.remove('roll-up', 'roll-down');
    void el.offsetWidth;
    el.classList.add(dir > 0 ? 'roll-up' : 'roll-down');
  }, { passive:false });

  document.getElementById('yearGo').addEventListener('click', function(){
    animateYearJump();
  });

  var monthCap = document.getElementById('monthCapsule');
  monthCap.addEventListener('click', function(e){
    var item = qclosest(e.target, '.month-item');
    if(item){
      var m = parseInt(item.getAttribute('data-month'), 10);
      if(m !== state.month){
        state.month = m;
        state.expandedWeekIndex = null;
        state.pendingTime = null;
        renderAll();
      }
    }
  });
  monthCap.addEventListener('wheel', function(e){
    e.preventDefault();
    changeMonth(e.deltaY < 0 ? -1 : 1, true);
  }, { passive:false });

  document.getElementById('markBtn').addEventListener('click', applyMark);
  document.getElementById('clearBtn').addEventListener('click', applyClear);

  document.getElementById('markBlocks').addEventListener('click', function(e){
    var x = qclosest(e.target, '.mark-block-x');
    if(x){
      var id = parseInt(x.getAttribute('data-id'), 10);
      state.selectedDates.forEach(function(k){
        if(dateMarks[k]){
          dateMarks[k] = dateMarks[k].filter(function(mid){ return mid !== id; });
          if(dateMarks[k].length===0) delete dateMarks[k];
        }
      });
      renderMonth();
      updateMarkBlocks();
      save();
    }
  });

  document.getElementById('markerList').addEventListener('dragleave', function(e){
    if(!this.contains(e.relatedTarget)) clearDropLine();
  });

  document.addEventListener('keydown', function(e){
    var tag = (document.activeElement && document.activeElement.tagName) || '';
    var inInput = (tag === 'INPUT' || tag === 'TEXTAREA' || tag === 'SELECT');
    if(e.code === 'Space'){
      if(inInput) return;
      var btn = document.getElementById('markBtn');
      if(btn.style.display !== 'none'){
        e.preventDefault();
        applyMark();
      }
    }
    if(e.key === 'z' || e.key === 'Z'){
      if(inInput) return;
      var cb = document.getElementById('clearBtn');
      if(cb.style.display !== 'none'){ applyClear(); }
    }
    if(e.key === 'Tab'){
      if(inInput) return;
      e.preventDefault();
      handleTabExpand();
    }
    if(e.key === 'Escape'){
      state.pendingTime = null;
      updatePendingSel();
      updateToolbar();
    }
  });

  var modalOverlay = document.getElementById('modalOverlay');
  document.getElementById('addBtn').addEventListener('click', openModal);
  document.getElementById('modalCancel').addEventListener('click', closeModal);
  document.getElementById('modalConfirm').addEventListener('click', confirmAdd);
  modalOverlay.addEventListener('mousedown', function(e){ if(e.target === modalOverlay) closeModal(); });
  document.getElementById('customColor').addEventListener('input', function(e){
    tempColor = e.target.value;
    document.getElementById('colorPreview').style.background = tempColor;
    clearPresetSelection();
  });
  document.getElementById('markerMeaning').addEventListener('keydown', function(e){
    if(e.key === 'Enter') confirmAdd();
  });

  document.getElementById('settingsBtn').addEventListener('click', openSettings);
  document.getElementById('saveWarningClose').addEventListener('click', function(){
    var el = document.getElementById('saveWarning');
    if(el) el.classList.remove('show');
  });
  document.getElementById('clearCalendarMarks').addEventListener('click', clearActiveCalendarMarks);
  document.getElementById('clearAllData').addEventListener('click', clearAllAppData);
  document.getElementById('storageRefresh').addEventListener('click', renderStorageInfo);
  document.getElementById('guideToggle').addEventListener('click', function(){
    var btn = document.getElementById('guideToggle');
    var body = document.getElementById('guideBody');
    if(!btn || !body) return;
    var willOpen = body.hasAttribute('hidden');
    if(willOpen){ body.removeAttribute('hidden'); } else { body.setAttribute('hidden', ''); }
    btn.setAttribute('aria-expanded', willOpen ? 'true' : 'false');
    btn.classList.toggle('open', willOpen);
    var txt = btn.querySelector('.guide-toggle-text');
    if(txt) txt.textContent = willOpen ? '收起' : '展开';
    if(willOpen && body.scrollIntoView){ try{ body.scrollIntoView({ block:'nearest' }); }catch(e){} }
  });
  document.getElementById('calAddBtn').addEventListener('click', function(){
    var inp = document.getElementById('calNewName');
    var name = inp.value.trim();
    var created = addCalendar(name);
    if(created){
      inp.value = '';
      renderSettings();
    }
  });
  document.getElementById('calNewName').addEventListener('keydown', function(e){
    if(e.key === 'Enter'){
      e.preventDefault();
      document.getElementById('calAddBtn').click();
    }
  });
  document.getElementById('settingsClose').addEventListener('click', closeSettings);
  document.getElementById('settingsX').addEventListener('click', closeSettings);
  document.getElementById('glassToggle').addEventListener('change', function(e){
    setGlass(e.target.checked);
  });
  document.getElementById('aiBtn').addEventListener('click', openAi);
  document.getElementById('aiClose').addEventListener('click', closeAi);
  document.getElementById('aiOverlay').addEventListener('mousedown', function(e){
    if(e.target === this) closeAi();
  });
  document.getElementById('settingsOverlay').addEventListener('mousedown', function(e){
    if(e.target === this) this.classList.remove('show');
  });
  document.getElementById('settingsStepAddBtn').addEventListener('click', function(){
    var v = parseInt(document.getElementById('settingsStepAddInput').value, 10);
    if(!isNaN(v) && v > 0 && stepPresets.indexOf(v) === -1){
      stepPresets.push(v);
      document.getElementById('settingsStepAddInput').value = '';
      renderSettings();
      renderStepOptions();
      save();
    }
  });
  document.getElementById('settingsOptionAddBtn').addEventListener('click', function(){
    var c = parseInt(document.getElementById('settingsOptionCount').value, 10);
    var raw = document.getElementById('settingsOptionLabels').value.trim();
    if(!raw) return;
    var labels = raw.split('/').map(function(s){ return s.trim(); }).filter(function(s){ return s.length > 0; });
    if(labels.length !== c){ alert('请填写 ' + c + ' 个选项（用/分隔）'); return; }
    if(!optionPresets[String(c)]) optionPresets[String(c)] = [];
    optionPresets[String(c)].push(labels);
    document.getElementById('settingsOptionLabels').value = '';
    renderSettings();
    save();
  });
  var modeBtns = document.querySelectorAll('.mode-btn');
  for(var mbi=0;mbi<modeBtns.length;mbi++){
    modeBtns[mbi].addEventListener('click', function(e){
      state.expandMode = e.currentTarget.getAttribute('data-mode');
      save();
      renderSettings();
      if(state.expandedWeekIndex !== null){
        state.detailJustExpanded = false;
        renderMonth();
      }
    });
  }
  var settingsTimer = null;
  var settingsBtnEl = document.getElementById('settingsBtn');
  settingsBtnEl.addEventListener('mouseenter', function(){
    settingsTimer = setTimeout(function(){
      var tip = document.getElementById('settingsTip');
      var r = settingsBtnEl.getBoundingClientRect();
      tip.style.right = '24px';
      tip.style.top = (r.bottom + 10) + 'px';
      tip.style.display = 'block';
    }, 1500);
  });
  settingsBtnEl.addEventListener('mouseleave', function(){
    clearTimeout(settingsTimer);
    document.getElementById('settingsTip').style.display = 'none';
  });

  document.getElementById('valuesAdd').addEventListener('click', function(){
    var el = document.getElementById('valueTypeChooser');
    if(el.style.display === 'none' || el.style.display === ''){
      renderTypeChooser();
    } else {
      el.style.display = 'none';
    }
  });
  document.getElementById('valuesSave').addEventListener('click', function(){
    saveValueEditor();
    closeValueEditor();
  });
  document.getElementById('valuesCancel').addEventListener('click', closeValueEditor);
  document.addEventListener('mousedown', function(e){
    var panel = document.getElementById('valuesPanel');
    if(panel && panel.style.display !== 'none' && !panel.contains(e.target)){
      closeValueEditor();
    }
  });
  var valuesDrag = { active:false, offX:0, offY:0 };
  document.getElementById('valuesPanel').addEventListener('mousedown', function(e){
    if(qclosest(e.target, '.values-panel-head')){
      valuesDrag.active = true;
      var rect = document.getElementById('valuesPanel').getBoundingClientRect();
      valuesDrag.offX = e.clientX - rect.left;
      valuesDrag.offY = e.clientY - rect.top;
      e.preventDefault();
    }
  });
  document.addEventListener('mousemove', function(e){
    if(valuesDrag.active){
      var panel = document.getElementById('valuesPanel');
      panel.style.left = (e.clientX - valuesDrag.offX) + 'px';
      panel.style.top = (e.clientY - valuesDrag.offY) + 'px';
    }
  });
  document.addEventListener('mouseup', function(){ valuesDrag.active = false; });

  var jYear = document.getElementById('jYear');
  var jMonth = document.getElementById('jMonth');
  var jDay = document.getElementById('jDay');
  var jumpGo = document.getElementById('jumpGo');
  function updateJump(){
    var filled = jYear.value.trim() !== '' && jMonth.value.trim() !== '' && jDay.value.trim() !== '';
    jumpGo.style.display = filled ? 'inline-block' : 'none';
  }
  jYear.addEventListener('input', updateJump);
  jMonth.addEventListener('input', updateJump);
  jDay.addEventListener('input', updateJump);
  jumpGo.addEventListener('click', function(){
    var y = parseInt(jYear.value, 10);
    var m = parseInt(jMonth.value, 10);
    var d = parseInt(jDay.value, 10);
    if(isNaN(y) || isNaN(m) || isNaN(d)){ alert('请输入有效的年月日'); return; }
    if(y < 1 || m < 1 || m > 12 || d < 1 || d > 31){ alert('请输入有效的年月日'); return; }
    var maxD = daysInMonth(y, m-1);
    if(d > maxD){ alert(y + '年' + m + '月最多 ' + maxD + ' 天'); return; }
    state.year = y; state.month = m-1;
    state.selYear = y;
    state.expandedWeekIndex = null;
    state.pendingTime = null;
    var key = dateKey(y, m-1, d);
    state.selectedDates = new Set([key]);
    state.anchorDate = key;
    renderAll();
  });

  /* 禁用浏览器默认拖拽（避免 Edge 拖拽搜索/打开） */
  document.addEventListener('dragover', function(e){ e.preventDefault(); });
  document.addEventListener('drop', function(e){ e.preventDefault(); });

  /* ---------- 初始化 ---------- */
  load();
  renderStepOptions();
  bindStepPanel();
  bindCalSwitcher();
  bindBgEvents();
  bindSettingsNav();
  renderAll();
  applyBackground();
  applyGlass();
  refreshImageList(function(){
    if(document.getElementById('settingsOverlay').classList.contains('show')){ renderBgSettings(); }
    applyBackground();
  });
})();
