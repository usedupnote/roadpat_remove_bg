'use strict';

/* ==========================================================
 * 배경 지우개 — 100% 브라우저 자체 엔진 (AI·서버 없음)
 *  - edge   : 가장자리와 이어진 배경만 제거 (플러드 필)
 *  - global : 배경색과 비슷한 픽셀 전체 제거
 *  - stamp  : 색→투명 변환(color-to-alpha), 도장·스캔에 최적
 * ========================================================== */

const $ = (sel) => document.querySelector(sel);

const els = {
  dropzone: $('#dropzone'),
  fileInput: $('#file-input'),
  editor: $('#editor'),
  srcCanvas: $('#src-canvas'),
  outCanvas: $('#out-canvas'),
  modeBtns: document.querySelectorAll('.mode-btn'),
  sliderRows: document.querySelectorAll('.slider-row'),
  tol: $('#tol'), tolVal: $('#tol-val'),
  soft: $('#soft'), softVal: $('#soft-val'),
  feather: $('#feather'), featherVal: $('#feather-val'),
  strength: $('#strength'), strengthVal: $('#strength-val'),
  despeckle: $('#despeckle'), despeckleVal: $('#despeckle-val'),
  swatch: $('#bg-swatch'),
  autoBg: $('#auto-bg'),
  download: $('#download'),
  trim: $('#trim'),
  exportScale: $('#export-scale'),
  denoise: $('#denoise'),
  sharpen: $('#sharpen'), sharpenVal: $('#sharpen-val'),
  status: $('#status'),
  srcPane: $('#src-pane'), outPane: $('#out-pane'),
  zoomIn: $('#zoom-in'), zoomOut: $('#zoom-out'), zoomFit: $('#zoom-fit'), zoomVal: $('#zoom-val'),
  brushBtns: document.querySelectorAll('.brush-btn'),
  shapeBtns: document.querySelectorAll('.shape-btn'),
  brushExtras: $('#brush-extras'),
  brushSize: $('#brush-size'), brushSizeVal: $('#brush-size-val'),
  brushUndo: $('#brush-undo'), brushRedo: $('#brush-redo'), brushClear: $('#brush-clear'),
};

const srcCtx = els.srcCanvas.getContext('2d', { willReadFrequently: true });
const outCtx = els.outCanvas.getContext('2d');

const state = {
  fileName: 'image',
  mode: 'edge',
  tol: 25,
  soft: 25,
  feather: 0,
  strength: 110,
  despeckle: 8,
  bg: { r: 255, g: 255, b: 255 },
  rawData: null,   // 업로드된 그대로의 원본 (화질 개선의 입력)
  median: false,   // 잡티 완화 (3x3 중앙값 필터)
  sharpen: 0,      // 선명하게 0~100 (언샤프 마스크)
  srcData: null,   // 화질 개선 적용된 작업 원본 — 엔진·브러시가 사용
  distMap: null,   // 배경색 기준 색 거리 캐시 (bg/이미지 변경 시 무효화)
  // 수동 보정 브러시: 엔진 결과와 분리된 편집 레이어라 재처리에도 유지됨
  brushTool: null, // null | 'erase' | 'restore'
  brushSize: 30,   // 지름(이미지 px)
  brushShape: 'circle', // 'circle' | 'square'
  zoom: 1,         // 1 = 패널 폭 맞춤, 최대 8배
  strokes: [],     // 획 목록 [{tool, size, points:[[x,y],...]}] — 되돌리기용
  redoStrokes: [], // 되돌린 획 보관 — 다시 실행용 (새 획을 그리면 비움)
  editMask: null,  // Uint8Array w*h: 0=없음 1=지움 2=복원
  engineOut: null, // 엔진 결과 ImageData (편집 미적용)
  workingOut: null,// 화면 표시 = engineOut + editMask
};

/* ---------- 색 거리 (redmean 가중 RGB, 0~255 스케일) ---------- */

function buildDistMap(data, bg) {
  const n = data.length >> 2;
  const map = new Float32Array(n);
  const { r: br, g: bg_, b: bb } = bg;
  for (let i = 0, p = 0; i < n; i++, p += 4) {
    const dr = data[p] - br, dg = data[p + 1] - bg_, db = data[p + 2] - bb;
    const rm = (data[p] + br) / 2;
    map[i] = Math.sqrt(((2 + rm / 256) * dr * dr + 4 * dg * dg + (2 + (255 - rm) / 256) * db * db) / 9);
  }
  return map;
}

/* ---------- 배경색 자동 감지: 테두리 픽셀의 최빈 색 ---------- */

function detectBg(data, w, h) {
  const buckets = new Map();
  const consider = (p) => {
    const key = ((data[p] >> 4) << 8) | ((data[p + 1] >> 4) << 4) | (data[p + 2] >> 4);
    let b = buckets.get(key);
    if (!b) { b = { n: 0, r: 0, g: 0, bl: 0 }; buckets.set(key, b); }
    b.n++; b.r += data[p]; b.g += data[p + 1]; b.bl += data[p + 2];
  };
  for (let x = 0; x < w; x++) { consider(x * 4); consider(((h - 1) * w + x) * 4); }
  for (let y = 1; y < h - 1; y++) { consider(y * w * 4); consider((y * w + w - 1) * 4); }
  let best = null;
  for (const b of buckets.values()) if (!best || b.n > best.n) best = b;
  return { r: Math.round(best.r / best.n), g: Math.round(best.g / best.n), b: Math.round(best.bl / best.n) };
}

/* ---------- edge 모드: 테두리에서 시작하는 플러드 필 ---------- */

function floodMask(distMap, w, h, threshold) {
  const mask = new Uint8Array(w * h);
  const stack = new Int32Array(w * h);
  let sp = 0;
  const seed = (i) => { if (!mask[i] && distMap[i] < threshold) { mask[i] = 1; stack[sp++] = i; } };
  for (let x = 0; x < w; x++) { seed(x); seed((h - 1) * w + x); }
  for (let y = 1; y < h - 1; y++) { seed(y * w); seed(y * w + w - 1); }
  while (sp > 0) {
    const i = stack[--sp];
    const x = i % w;
    if (x > 0)          { const j = i - 1; if (!mask[j] && distMap[j] < threshold) { mask[j] = 1; stack[sp++] = j; } }
    if (x < w - 1)      { const j = i + 1; if (!mask[j] && distMap[j] < threshold) { mask[j] = 1; stack[sp++] = j; } }
    if (i >= w)         { const j = i - w; if (!mask[j] && distMap[j] < threshold) { mask[j] = 1; stack[sp++] = j; } }
    if (i < w * (h - 1)) { const j = i + w; if (!mask[j] && distMap[j] < threshold) { mask[j] = 1; stack[sp++] = j; } }
  }
  return mask;
}

/* ---------- 색 키 제거: tol 이하 완전 투명, tol~tol+soft 반투명 ----------
 * 반투명 구간은 배경색 성분을 역산(unblend)해 흰 테두리(halo)를 없앤다. */

function applyKey(data, distMap, mask, tol, soft, bg) {
  const n = distMap.length;
  const band = Math.max(soft, 0.001);
  for (let i = 0, p = 0; i < n; i++, p += 4) {
    if (mask && !mask[i]) continue;
    const d = distMap[i];
    if (d <= tol) { data[p + 3] = 0; continue; }
    const t = (d - tol) / band;
    if (t >= 1) continue;
    data[p]     = clamp255((data[p]     - bg.r * (1 - t)) / t);
    data[p + 1] = clamp255((data[p + 1] - bg.g * (1 - t)) / t);
    data[p + 2] = clamp255((data[p + 2] - bg.b * (1 - t)) / t);
    data[p + 3] = Math.round(t * data[p + 3]);
  }
}

/* ---------- stamp 모드: color-to-alpha ----------
 * 배경색과의 채널별 차이를 투명도로 변환하고 잉크 원색을 역산.
 * 반투명한 인영·안티앨리어싱 가장자리가 자연스럽게 살아난다. */

function colorToAlpha(data, bg, strength, despeckle) {
  const k = strength / 100;
  const cut = despeckle / 100; // 이 비율 이하의 옅은 흔적(스캔 노이즈)은 제거
  for (let p = 0; p < data.length; p += 4) {
    let amax = 0;
    for (let c = 0; c < 3; c++) {
      const v = data[p + c];
      const b = c === 0 ? bg.r : c === 1 ? bg.g : bg.b;
      const ac = v > b ? (v - b) / (255 - b || 1) : (b - v) / (b || 1);
      if (ac > amax) amax = ac;
    }
    const a = (amax - cut) / (1 - cut);
    if (a <= 0.004) { data[p + 3] = 0; continue; }
    // 원색 복원은 순수 amax로, 최종 투명도에만 잡티 제거·진하기 반영
    data[p]     = clamp255(bg.r + (data[p]     - bg.r) / amax);
    data[p + 1] = clamp255(bg.g + (data[p + 1] - bg.g) / amax);
    data[p + 2] = clamp255(bg.b + (data[p + 2] - bg.b) / amax);
    data[p + 3] = Math.round(Math.min(1, a * k) * data[p + 3]);
  }
}

/* ---------- 알파 채널 박스 블러 (가장자리 흐림) ---------- */

function blurAlpha(data, w, h, r) {
  const n = w * h;
  const a = new Float32Array(n);
  for (let i = 0; i < n; i++) a[i] = data[i * 4 + 3];
  const tmp = new Float32Array(n);
  for (let y = 0; y < h; y++) {          // 가로
    const row = y * w;
    for (let x = 0; x < w; x++) {
      let sum = 0, cnt = 0;
      for (let k = -r; k <= r; k++) {
        const xx = x + k;
        if (xx >= 0 && xx < w) { sum += a[row + xx]; cnt++; }
      }
      tmp[row + x] = sum / cnt;
    }
  }
  for (let x = 0; x < w; x++) {          // 세로
    for (let y = 0; y < h; y++) {
      let sum = 0, cnt = 0;
      for (let k = -r; k <= r; k++) {
        const yy = y + k;
        if (yy >= 0 && yy < h) { sum += tmp[yy * w + x]; cnt++; }
      }
      data[(y * w + x) * 4 + 3] = Math.round(sum / cnt);
    }
  }
}

function clamp255(v) { return v < 0 ? 0 : v > 255 ? 255 : Math.round(v); }

/* ---------- 처리 파이프라인 ---------- */

function process() {
  if (!state.srcData) return;
  const t0 = performance.now();
  const w = state.srcData.width, h = state.srcData.height;
  const out = new ImageData(new Uint8ClampedArray(state.srcData.data), w, h);

  if (state.mode === 'stamp') {
    colorToAlpha(out.data, state.bg, state.strength, state.despeckle);
  } else {
    if (!state.distMap) state.distMap = buildDistMap(state.srcData.data, state.bg);
    const threshold = Math.max(state.tol + state.soft, 1);
    const mask = state.mode === 'edge' ? floodMask(state.distMap, w, h, threshold) : null;
    applyKey(out.data, state.distMap, mask, state.tol, state.soft, state.bg);
    if (state.feather > 0) blurAlpha(out.data, w, h, state.feather);
  }

  state.engineOut = out;
  state.workingOut = new ImageData(new Uint8ClampedArray(out.data), w, h);
  if (state.editMask) applyEditMaskAll();
  outCtx.putImageData(state.workingOut, 0, 0);
  const ms = Math.round(performance.now() - t0);
  setStatus(`${w}×${h}px · 처리 ${ms}ms · 배경색 rgb(${state.bg.r}, ${state.bg.g}, ${state.bg.b})`);
}

// rAF는 탭이 가려지면 멈추므로 setTimeout으로 디바운스
let pending = false;
function scheduleProcess() {
  if (pending) return;
  pending = true;
  setTimeout(() => { pending = false; process(); }, 16);
}

function setStatus(msg) { els.status.textContent = msg; }

/* ---- 사용 통계 (Google Analytics — index.html에서 로드, 로컬에선 미로드) ---- */
function track(name, params) {
  if (typeof gtag === 'function') gtag('event', name, params);
}

function updateSwatch() {
  els.swatch.style.background = `rgb(${state.bg.r}, ${state.bg.g}, ${state.bg.b})`;
}

/* ---------- 이미지 로드 ---------- */

function loadFromSrc(src, name) {
  const img = new Image();
  img.onload = () => {
    state.fileName = (name || 'image').replace(/\.[^.]+$/, '');
    const w = img.naturalWidth, h = img.naturalHeight;
    els.srcCanvas.width = w; els.srcCanvas.height = h;
    els.outCanvas.width = w; els.outCanvas.height = h;
    srcCtx.drawImage(img, 0, 0);
    state.rawData = srcCtx.getImageData(0, 0, w, h);
    state.srcData = buildEnhanced();
    srcCtx.putImageData(state.srcData, 0, 0);
    state.distMap = null;
    state.editMask = new Uint8Array(w * h);
    state.strokes = [];
    state.redoStrokes = [];
    state.bg = detectBg(state.srcData.data, w, h);
    updateSwatch();
    updateBrushUI();
    updateBrushCursor();
    els.dropzone.classList.add('compact');
    els.editor.hidden = false;
    state.zoom = 1;
    applyView();
    process();
  };
  img.onerror = () => setStatus('이미지를 불러올 수 없습니다. 다른 파일로 시도해 주세요.');
  img.src = src;
}

function loadFile(file, source) {
  if (!file || !file.type.startsWith('image/')) return;
  const reader = new FileReader();
  reader.onload = () => loadFromSrc(reader.result, file.name);
  reader.readAsDataURL(file);
  track('image_load', { source: source || 'file' });
}

/* ---------- 이벤트 연결 ---------- */

els.dropzone.addEventListener('click', () => els.fileInput.click());
els.fileInput.addEventListener('change', () => loadFile(els.fileInput.files[0], 'picker'));

window.addEventListener('dragover', (e) => { e.preventDefault(); els.dropzone.classList.add('dragover'); });
window.addEventListener('dragleave', () => els.dropzone.classList.remove('dragover'));
window.addEventListener('drop', (e) => {
  e.preventDefault();
  els.dropzone.classList.remove('dragover');
  loadFile(e.dataTransfer.files[0], 'drop');
});

window.addEventListener('paste', (e) => {
  for (const item of e.clipboardData.items) {
    if (item.type.startsWith('image/')) { loadFile(item.getAsFile(), 'paste'); return; }
  }
});

els.modeBtns.forEach((btn) => btn.addEventListener('click', () => {
  state.mode = btn.dataset.mode;
  track('mode_change', { mode: state.mode });
  els.modeBtns.forEach((b) => b.classList.toggle('active', b === btn));
  els.sliderRows.forEach((row) => { row.hidden = !row.dataset.modes.split(' ').includes(state.mode); });
  scheduleProcess();
}));

function bindSlider(input, output, key) {
  input.addEventListener('input', () => {
    state[key] = Number(input.value);
    output.value = input.value;
    scheduleProcess();
  });
}
bindSlider(els.tol, els.tolVal, 'tol');
bindSlider(els.soft, els.softVal, 'soft');
bindSlider(els.feather, els.featherVal, 'feather');
bindSlider(els.strength, els.strengthVal, 'strength');
bindSlider(els.despeckle, els.despeckleVal, 'despeckle');

els.srcCanvas.addEventListener('click', (e) => {
  if (!state.srcData) return;
  if (didPan) return; // 드래그 이동 직후엔 스포이드 동작 안 함
  const rect = els.srcCanvas.getBoundingClientRect();
  const x = Math.floor((e.clientX - rect.left) * els.srcCanvas.width / rect.width);
  const y = Math.floor((e.clientY - rect.top) * els.srcCanvas.height / rect.height);
  const p = srcCtx.getImageData(x, y, 1, 1).data;
  state.bg = { r: p[0], g: p[1], b: p[2] };
  state.distMap = null;
  updateSwatch();
  scheduleProcess();
});

/* ---------- 화질 개선 (배경 제거 전 원본에 적용) ---------- */

// 3x3 중앙값 필터 — JPEG 압축 잡티·점 노이즈 정리 (RGB만, 알파 유지)
function medianFilter(img) {
  const { data, width: w, height: h } = img;
  const src = new Uint8ClampedArray(data);
  const buf = new Uint8Array(9);
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      const p = (y * w + x) * 4;
      for (let c = 0; c < 3; c++) {
        let n = 0;
        for (let dy = -1; dy <= 1; dy++) {
          const yy = dy < 0 ? Math.max(0, y + dy) : Math.min(h - 1, y + dy);
          for (let dx = -1; dx <= 1; dx++) {
            const xx = dx < 0 ? Math.max(0, x + dx) : Math.min(w - 1, x + dx);
            buf[n++] = src[(yy * w + xx) * 4 + c];
          }
        }
        // 9개 삽입 정렬 후 중앙값
        for (let i = 1; i < 9; i++) {
          const v = buf[i]; let j = i - 1;
          while (j >= 0 && buf[j] > v) { buf[j + 1] = buf[j]; j--; }
          buf[j + 1] = v;
        }
        data[p + c] = buf[4];
      }
    }
  }
}

// 3x3 평균 블러 (RGB) — 언샤프 마스크용
function blur3x3RGB(src, w, h) {
  const out = new Uint8ClampedArray(src.length);
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      const p = (y * w + x) * 4;
      for (let c = 0; c < 3; c++) {
        let sum = 0;
        for (let dy = -1; dy <= 1; dy++) {
          const yy = dy < 0 ? Math.max(0, y + dy) : Math.min(h - 1, y + dy);
          for (let dx = -1; dx <= 1; dx++) {
            const xx = dx < 0 ? Math.max(0, x + dx) : Math.min(w - 1, x + dx);
            sum += src[(yy * w + xx) * 4 + c];
          }
        }
        out[p + c] = sum / 9;
      }
    }
  }
  return out;
}

// 언샤프 마스크: 원본 + amount x (원본 - 블러) → 경계 대비 강화
function unsharp(img, amount) {
  const { data, width: w, height: h } = img;
  const blurred = blur3x3RGB(data, w, h);
  for (let p = 0; p < data.length; p += 4) {
    for (let c = 0; c < 3; c++) {
      data[p + c] = clamp255(data[p + c] + amount * (data[p + c] - blurred[p + c]));
    }
  }
}

function buildEnhanced() {
  const img = new ImageData(new Uint8ClampedArray(state.rawData.data), state.rawData.width, state.rawData.height);
  if (state.median) medianFilter(img);
  if (state.sharpen > 0) unsharp(img, state.sharpen / 50); // 0~2.0
  return img;
}

// 화질 설정 변경 시: 작업 원본 재구성 → 원본 캔버스 갱신 → 엔진 재처리 (브러시 보정은 유지됨)
function applyEnhance() {
  if (!state.rawData) return;
  state.srcData = buildEnhanced();
  srcCtx.putImageData(state.srcData, 0, 0);
  state.distMap = null;
  process();
}

let enhancePending = null;
function scheduleEnhance() {
  clearTimeout(enhancePending);
  enhancePending = setTimeout(applyEnhance, 150);
}

els.denoise.addEventListener('click', () => {
  state.median = !state.median;
  els.denoise.classList.toggle('active', state.median);
  scheduleEnhance();
});

els.sharpen.addEventListener('input', () => {
  state.sharpen = Number(els.sharpen.value);
  els.sharpenVal.value = els.sharpen.value;
  scheduleEnhance();
});

/* ---------- 수동 보정 브러시 ----------
 * 결과 캔버스를 문질러 지우개(투명)/복원(원본) 편집.
 * 편집은 editMask에 기록되어 엔진 재처리 후에도 유지된다. */

function applyEditMaskAll() {
  const m = state.editMask, wo = state.workingOut.data, src = state.srcData.data;
  for (let i = 0, p = 0; i < m.length; i++, p += 4) {
    if (m[i] === 1) wo[p + 3] = 0;
    else if (m[i] === 2) { wo[p] = src[p]; wo[p + 1] = src[p + 1]; wo[p + 2] = src[p + 2]; wo[p + 3] = src[p + 3]; }
  }
}

function paintStamp(cx, cy, radius, tool, shape) {
  const w = state.srcData.width, h = state.srcData.height;
  const m = state.editMask, wo = state.workingOut.data, src = state.srcData.data;
  const val = tool === 'erase' ? 1 : 2;
  const square = shape === 'square';
  const x0 = Math.max(0, Math.floor(cx - radius)), x1 = Math.min(w - 1, Math.ceil(cx + radius));
  const y0 = Math.max(0, Math.floor(cy - radius)), y1 = Math.min(h - 1, Math.ceil(cy + radius));
  const r2 = radius * radius;
  for (let y = y0; y <= y1; y++) {
    const dy = y - cy;
    for (let x = x0; x <= x1; x++) {
      const dx = x - cx;
      if (!square && dx * dx + dy * dy > r2) continue;
      const i = y * w + x, p = i * 4;
      m[i] = val;
      if (val === 1) { wo[p + 3] = 0; }
      else { wo[p] = src[p]; wo[p + 1] = src[p + 1]; wo[p + 2] = src[p + 2]; wo[p + 3] = src[p + 3]; }
    }
  }
  return [x0, y0, x1 - x0 + 1, y1 - y0 + 1];
}

function stampSegment(x0, y0, x1, y1, radius, tool, shape) {
  const dist = Math.hypot(x1 - x0, y1 - y0);
  const steps = Math.max(1, Math.ceil(dist / Math.max(radius / 2, 1)));
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  for (let s = 0; s <= steps; s++) {
    const t = s / steps;
    const [rx, ry, rw, rh] = paintStamp(x0 + (x1 - x0) * t, y0 + (y1 - y0) * t, radius, tool, shape);
    if (rw <= 0 || rh <= 0) continue;
    minX = Math.min(minX, rx); minY = Math.min(minY, ry);
    maxX = Math.max(maxX, rx + rw); maxY = Math.max(maxY, ry + rh);
  }
  if (maxX > minX && maxY > minY) {
    outCtx.putImageData(state.workingOut, 0, 0, minX, minY, maxX - minX, maxY - minY);
  }
}

function rebuildEdits() {
  if (!state.srcData) return;
  state.editMask.fill(0);
  state.workingOut = new ImageData(new Uint8ClampedArray(state.engineOut.data), state.engineOut.width, state.engineOut.height);
  for (const st of state.strokes) {
    const r = st.size / 2;
    let prev = st.points[0];
    for (const pt of st.points) {
      const dist = Math.hypot(pt[0] - prev[0], pt[1] - prev[1]);
      const steps = Math.max(1, Math.ceil(dist / Math.max(r / 2, 1)));
      for (let s = 0; s <= steps; s++) {
        const t = s / steps;
        paintStamp(prev[0] + (pt[0] - prev[0]) * t, prev[1] + (pt[1] - prev[1]) * t, r, st.tool, st.shape);
      }
      prev = pt;
    }
  }
  outCtx.putImageData(state.workingOut, 0, 0);
  updateBrushUI();
}

function canvasPos(e) {
  const rect = els.outCanvas.getBoundingClientRect();
  return [
    (e.clientX - rect.left) * els.outCanvas.width / rect.width,
    (e.clientY - rect.top) * els.outCanvas.height / rect.height,
  ];
}

let activeStroke = null;

els.outCanvas.addEventListener('pointerdown', (e) => {
  if (!state.brushTool || !state.srcData) return;
  e.preventDefault();
  try { els.outCanvas.setPointerCapture(e.pointerId); } catch (_) {}
  const [x, y] = canvasPos(e);
  activeStroke = { tool: state.brushTool, size: state.brushSize, shape: state.brushShape, points: [[x, y]] };
  stampSegment(x, y, x, y, state.brushSize / 2, state.brushTool, state.brushShape);
});

els.outCanvas.addEventListener('pointermove', (e) => {
  if (!activeStroke) return;
  const [x, y] = canvasPos(e);
  const last = activeStroke.points[activeStroke.points.length - 1];
  activeStroke.points.push([x, y]);
  stampSegment(last[0], last[1], x, y, activeStroke.size / 2, activeStroke.tool, activeStroke.shape);
});

function endStroke() {
  if (!activeStroke) return;
  state.strokes.push(activeStroke);
  state.redoStrokes = []; // 새 획을 그리면 다시 실행 이력은 무효
  activeStroke = null;
  updateBrushUI();
}
els.outCanvas.addEventListener('pointerup', endStroke);
els.outCanvas.addEventListener('pointercancel', endStroke);

function updateBrushUI() {
  els.brushExtras.hidden = !state.brushTool && !state.strokes.length && !state.redoStrokes.length;
  els.brushUndo.disabled = !state.strokes.length;
  els.brushRedo.disabled = !state.redoStrokes.length;
}

function updateBrushCursor() {
  if (!state.brushTool || !state.srcData) {
    els.outCanvas.style.cursor = '';
    els.outCanvas.style.touchAction = '';
    return;
  }
  const rect = els.outCanvas.getBoundingClientRect();
  const scale = rect.width && els.outCanvas.width ? rect.width / els.outCanvas.width : 1;
  const d = Math.round(Math.max(6, Math.min(127, state.brushSize * scale)));
  const r = d / 2;
  const color = state.brushTool === 'erase' ? '#d64541' : '#007DC5';
  const inner = state.brushShape === 'square'
    ? `<rect x="1" y="1" width="${d - 2}" height="${d - 2}" fill="none" stroke="${color}" stroke-width="1.5"/>`
    : `<circle cx="${r}" cy="${r}" r="${r - 1}" fill="none" stroke="${color}" stroke-width="1.5"/>`;
  const svg = `<svg xmlns="http://www.w3.org/2000/svg" width="${d}" height="${d}">${inner}</svg>`;
  els.outCanvas.style.cursor = `url('data:image/svg+xml;utf8,${encodeURIComponent(svg)}') ${Math.floor(r)} ${Math.floor(r)}, crosshair`;
  els.outCanvas.style.touchAction = 'none'; // 터치 드로잉 중 스크롤 방지
}

els.brushBtns.forEach((btn) => btn.addEventListener('click', () => {
  const tool = btn.dataset.tool;
  state.brushTool = state.brushTool === tool ? null : tool;
  els.brushBtns.forEach((b) => b.classList.toggle('active', b.dataset.tool === state.brushTool));
  updateBrushUI();
  updateBrushCursor();
  if (state.brushTool) track('brush_enable', { tool: state.brushTool });
}));

els.brushSize.addEventListener('input', () => {
  state.brushSize = Number(els.brushSize.value);
  els.brushSizeVal.value = els.brushSize.value;
  updateBrushCursor();
});

els.shapeBtns.forEach((btn) => btn.addEventListener('click', () => {
  state.brushShape = btn.dataset.shape;
  els.shapeBtns.forEach((b) => b.classList.toggle('active', b === btn));
  updateBrushCursor();
}));

function undoStroke() {
  if (!state.strokes.length) return;
  state.redoStrokes.push(state.strokes.pop());
  rebuildEdits();
}

function redoStroke() {
  if (!state.redoStrokes.length) return;
  state.strokes.push(state.redoStrokes.pop());
  rebuildEdits();
}

els.brushUndo.addEventListener('click', undoStroke);
els.brushRedo.addEventListener('click', redoStroke);

els.brushClear.addEventListener('click', () => {
  if (!state.strokes.length && !state.redoStrokes.length) return;
  state.strokes = [];
  state.redoStrokes = [];
  rebuildEdits();
});

// Ctrl+Z 되돌리기 / Ctrl+Shift+Z·Ctrl+Y 다시 실행 (Mac ⌘ 포함)
window.addEventListener('keydown', (e) => {
  if (!state.srcData) return;
  if (!(e.ctrlKey || e.metaKey)) return;
  const key = e.key.toLowerCase();
  if (key === 'z') {
    e.preventDefault();
    if (e.shiftKey) redoStroke(); else undoStroke();
  } else if (key === 'y') {
    e.preventDefault();
    redoStroke();
  }
});

/* ---------- 보기: 폭 맞춤 + 확대·축소 + 동기화 이동 ----------
 * 캔버스 픽셀은 그대로 두고 CSS 폭만 바꾸는 방식이라
 * 엔진·브러시의 좌표 변환(rect 기반)이 자동으로 맞는다. */

function applyView() {
  if (!state.srcData) return;
  const paneW = els.srcPane.clientWidth || state.srcData.width;
  const cssW = Math.round(paneW * state.zoom);
  els.srcCanvas.style.width = cssW + 'px';
  els.outCanvas.style.width = cssW + 'px';
  const pixelScale = cssW / state.srcData.width;
  els.srcCanvas.classList.toggle('pixelated', pixelScale >= 2);
  els.outCanvas.classList.toggle('pixelated', pixelScale >= 2);
  els.zoomVal.value = Math.round(state.zoom * 100) + '%';
  updateBrushCursor();
}

function setZoomAnchored(z, clientX, clientY, pane) {
  z = Math.min(8, Math.max(1, z));
  if (!state.srcData) return;
  const p = pane || els.srcPane;
  const rect = p.getBoundingClientRect();
  const ax = clientX !== undefined ? clientX - rect.left : rect.width / 2;
  const ay = clientY !== undefined ? clientY - rect.top : rect.height / 2;
  const k = z / state.zoom;
  const sl = (p.scrollLeft + ax) * k - ax;
  const st = (p.scrollTop + ay) * k - ay;
  state.zoom = z;
  applyView();
  els.srcPane.scrollLeft = els.outPane.scrollLeft = sl;
  els.srcPane.scrollTop = els.outPane.scrollTop = st;
}

els.zoomIn.addEventListener('click', () => setZoomAnchored(state.zoom * 1.5));
els.zoomOut.addEventListener('click', () => setZoomAnchored(state.zoom / 1.5));
els.zoomFit.addEventListener('click', () => setZoomAnchored(1));

// Ctrl+휠(트랙패드 핀치 포함)로 커서 위치 기준 확대·축소
[els.srcPane, els.outPane].forEach((pane) => {
  pane.addEventListener('wheel', (e) => {
    if (!e.ctrlKey) return;
    e.preventDefault();
    const k = e.deltaY < 0 ? 1.2 : 1 / 1.2;
    setZoomAnchored(state.zoom * k, e.clientX, e.clientY, pane);
  }, { passive: false });
});

// 양쪽 패널 스크롤 동기화 — 스크롤바·휠 등 네이티브 스크롤용
// (팬 드래그·줌은 위에서 양쪽을 직접 쓰므로 여기 의존하지 않음)
let syncingScroll = false;
function bindScrollSync(a, b) {
  a.addEventListener('scroll', () => {
    if (syncingScroll) return;
    syncingScroll = true;
    b.scrollLeft = a.scrollLeft;
    b.scrollTop = a.scrollTop;
    setTimeout(() => { syncingScroll = false; }, 0);
  });
}
bindScrollSync(els.srcPane, els.outPane);
bindScrollSync(els.outPane, els.srcPane);

// 마우스 드래그로 이동 (터치는 기본 스크롤 사용, 브러시 사용 중엔 브러시 우선)
let panState = null;
let didPan = false;
function bindPan(pane) {
  pane.addEventListener('pointerdown', (e) => {
    if (e.pointerType !== 'mouse') return;
    if (e.button !== 0 && e.button !== 1) return;
    if (pane === els.outPane && state.brushTool && e.button === 0) return;
    panState = { pane, x: e.clientX, y: e.clientY, sl: pane.scrollLeft, st: pane.scrollTop, id: e.pointerId };
    didPan = false;
    // 주의: 여기서 setPointerCapture를 걸면 click 이벤트가 패널로 넘어가
    // 캔버스의 스포이드 클릭이 죽는다 — 실제 드래그 시작 후에만 캡처
  });
  pane.addEventListener('pointermove', (e) => {
    if (!panState || panState.pane !== pane) return;
    const dx = e.clientX - panState.x, dy = e.clientY - panState.y;
    if (!didPan && Math.abs(dx) + Math.abs(dy) > 4) {
      didPan = true;
      try { pane.setPointerCapture(panState.id); } catch (_) {}
    }
    if (!didPan) return;
    // 양쪽 패널을 직접 동시에 이동 (scroll 이벤트에 의존하지 않음)
    els.srcPane.scrollLeft = els.outPane.scrollLeft = panState.sl - dx;
    els.srcPane.scrollTop = els.outPane.scrollTop = panState.st - dy;
    pane.style.cursor = 'grabbing';
  });
  const endPan = () => {
    if (!panState || panState.pane !== pane) return;
    panState = null;
    pane.style.cursor = '';
    setTimeout(() => { didPan = false; }, 0); // click(스포이드)보다 늦게 해제
  };
  pane.addEventListener('pointerup', endPan);
  pane.addEventListener('pointercancel', endPan);
}
bindPan(els.srcPane);
bindPan(els.outPane);

window.addEventListener('resize', () => { applyView(); updateBrushCursor(); });

els.autoBg.addEventListener('click', () => {
  if (!state.srcData) return;
  state.bg = detectBg(state.srcData.data, state.srcData.width, state.srcData.height);
  state.distMap = null;
  updateSwatch();
  scheduleProcess();
});

/* ---- 내보내기: 투명 여백 잘라내기 ----
 * 원본에서 개체가 한쪽에 몰려 있으면 투명 여백도 그대로 따라가므로,
 * 불투명 픽셀의 경계 상자(bbox)로 잘라 개체 기준으로 저장한다. */

function contentBBox(imageData) {
  const { data, width: w, height: h } = imageData;
  let minX = w, minY = h, maxX = -1, maxY = -1;
  for (let y = 0; y < h; y++) {
    const row = y * w;
    for (let x = 0; x < w; x++) {
      if (data[(row + x) * 4 + 3] !== 0) {
        if (x < minX) minX = x;
        if (x > maxX) maxX = x;
        if (y < minY) minY = y;
        maxY = y;
      }
    }
  }
  if (maxX < 0) return null; // 전부 투명
  return { x: minX, y: minY, w: maxX - minX + 1, h: maxY - minY + 1 };
}

function buildExportCanvas() {
  let base = els.outCanvas;
  if (els.trim.checked) {
    const w = els.outCanvas.width, h = els.outCanvas.height;
    const img = outCtx.getImageData(0, 0, w, h);
    const box = contentBBox(img);
    if (box && (box.w !== w || box.h !== h)) {
      const c = document.createElement('canvas');
      c.width = box.w; c.height = box.h;
      c.getContext('2d').putImageData(img, -box.x, -box.y);
      base = c;
    }
  }
  const scale = Number(els.exportScale.value) || 1;
  if (scale > 1) {
    const up = document.createElement('canvas');
    up.width = base.width * scale; up.height = base.height * scale;
    const g = up.getContext('2d');
    g.imageSmoothingEnabled = true;
    g.imageSmoothingQuality = 'high';
    g.drawImage(base, 0, 0, up.width, up.height);
    return up;
  }
  return base;
}

els.download.addEventListener('click', () => {
  const scale = Number(els.exportScale.value) || 1;
  track('download', { mode: state.mode, trim: els.trim.checked ? 'on' : 'off', scale });
  buildExportCanvas().toBlob((blob) => {
    const a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = `${state.fileName}_transparent${scale > 1 ? '@' + scale + 'x' : ''}.png`;
    a.click();
    setTimeout(() => URL.revokeObjectURL(a.href), 5000);
  }, 'image/png');
});

// 초기 슬라이더 표시 상태 동기화
els.sliderRows.forEach((row) => { row.hidden = !row.dataset.modes.split(' ').includes(state.mode); });
updateSwatch();

// 디버그·테스트용 훅
window.__bgApp = { state, loadFromSrc, process, buildExportCanvas };
