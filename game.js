'use strict';

const COLS = 10;
const ROWS = 20;
const BLOCK = 30;

const COLORS = [
  null,
  '#4dd0e1', // I - cyan
  '#ffd54f', // O - yellow
  '#ba68c8', // T - purple
  '#81c784', // S - green
  '#e57373', // Z - red
  '#90caf9', // J - pale blue
  '#ffb74d', // L - orange
  '#cfd8dc', // 8 - comodín (se dibuja con degradado, ver drawBlock)
];

// ---- Piezas especiales ----
const SPECIAL_EVERY_LINES = 10;   // líneas completas necesarias para ganar una pieza especial
const FREEZE_DURATION_MS = 5000;  // duración del efecto Congelar (tiempo de juego activo)
const WILD = 8;                   // valor de celda para los bloques comodín (Tinte)
const DEBUG_SPECIALS = false;     // true, o añadir ?debug a la URL, activa el modo depuración

const SPECIAL_EFFECTS = {
  bomb:    { icon: '💣', name: 'Bomba' },
  ray:     { icon: '⚡', name: 'Rayo' },
  tint:    { icon: '🎨', name: 'Tinte' },
  gravity: { icon: '🌀', name: 'Gravedad' },
  freeze:  { icon: '❄️', name: 'Congelar' },
};
const EFFECT_KEYS = Object.keys(SPECIAL_EFFECTS);
const DEBUG = DEBUG_SPECIALS || /[?&]debug/.test(location.search);

const PIECES = [
  null,
  [[0,0,0,0],[1,1,1,1],[0,0,0,0],[0,0,0,0]], // I
  [[2,2],[2,2]],                               // O
  [[0,3,0],[3,3,3],[0,0,0]],                  // T
  [[0,4,4],[4,4,0],[0,0,0]],                  // S
  [[5,5,0],[0,5,5],[0,0,0]],                  // Z
  [[6,0,0],[6,6,6],[0,0,0]],                  // J
  [[0,0,7],[7,7,7],[0,0,0]],                  // L
];

const GHOST = 'ghost';

// ---- Tema claro/oscuro ----
const themeVars = { grid: '#22222e', shine: 'rgba(255,255,255,0.12)', ghostAlpha: 0.2 };

function readThemeVars() {
  const cs = getComputedStyle(document.documentElement);
  themeVars.grid = cs.getPropertyValue('--grid').trim() || themeVars.grid;
  themeVars.shine = cs.getPropertyValue('--block-shine').trim() || themeVars.shine;
  themeVars.ghostAlpha = parseFloat(cs.getPropertyValue('--ghost-alpha')) || themeVars.ghostAlpha;
}

const LINE_SCORES = [0, 100, 300, 500, 800];

// ---- Puntos de enganche (cada funcionalidad añade sus funciones con HOOKS.<evento>.push(fn)) ----
const HOOKS = {
  init: [],      // () al final de init(): nueva partida
  gameOver: [],  // () al final de endGame()
  locked: [],    // (cleared) tras fijar una pieza y limpiar líneas
  key: [],       // (e) al inicio del keydown; devolver true consume la tecla
};
const runHooks = (name, ...args) => HOOKS[name].forEach(fn => fn(...args));

const canvas = document.getElementById('board');
const ctx = canvas.getContext('2d');
const nextCanvas = document.getElementById('next-canvas');
const nextCtx = nextCanvas.getContext('2d');
const scoreEl = document.getElementById('score');
const linesEl = document.getElementById('lines');
const levelEl = document.getElementById('level');
const overlay = document.getElementById('overlay');
const overlayTitle = document.getElementById('overlay-title');
const overlayScore = document.getElementById('overlay-score');
const restartBtn = document.getElementById('restart-btn');
const specialLeftEl = document.getElementById('special-left');
const specialQueueEl = document.getElementById('special-queue');
const freezeIndicator = document.getElementById('freeze-indicator');
const freezeTimeEl = document.getElementById('freeze-time');
const debugBadge = document.getElementById('debug-badge');

let board, current, next, score, lines, level, paused, gameOver, lastTime, dropAccum, dropInterval, animId;
// Estado de piezas especiales
let pendingSpecials = [];   // efectos ganados y aún no entregados (en orden)
let linesTowardSpecial = 0; // líneas completas acumuladas hacia la próxima pieza especial
let freezeMs = 0;           // tiempo restante de Congelar (ms de juego activo)
let fx = [];                // animaciones breves en curso
let lastFreezeText = '';

function createBoard() {
  return Array.from({ length: ROWS }, () => new Array(COLS).fill(0));
}

// Bloque "núcleo": la celda ocupada más cercana al centro de la forma (lleva el icono).
function coreCell(shape) {
  let sr = 0, sc = 0, n = 0;
  for (let r = 0; r < shape.length; r++)
    for (let c = 0; c < shape[r].length; c++)
      if (shape[r][c]) { sr += r; sc += c; n++; }
  const cr = sr / n, cc = sc / n;
  let best = null, bestD = Infinity;
  for (let r = 0; r < shape.length; r++)
    for (let c = 0; c < shape[r].length; c++) {
      if (!shape[r][c]) continue;
      const d = (r - cr) ** 2 + (c - cc) ** 2;
      if (d < bestD) { bestD = d; best = { r, c }; }
    }
  return best;
}

function makePiece(type, effect) {
  const shape = PIECES[type].map(row => [...row]);
  const piece = { type, shape, x: Math.floor(COLS / 2) - Math.floor(shape[0].length / 2), y: 0 };
  if (effect) piece.special = { effect, ...coreCell(shape) };
  return piece;
}

function randomType() {
  return Math.floor(Math.random() * 7) + 1;
}

function randomPiece() {
  return makePiece(randomType());
}

// Entrega en orden las recompensas pendientes; si no hay, pieza normal.
function nextPiece() {
  if (pendingSpecials.length) return makePiece(randomType(), pendingSpecials.shift());
  return randomPiece();
}

function collide(shape, ox, oy) {
  for (let r = 0; r < shape.length; r++) {
    for (let c = 0; c < shape[r].length; c++) {
      if (!shape[r][c]) continue;
      const nx = ox + c;
      const ny = oy + r;
      if (nx < 0 || nx >= COLS || ny >= ROWS) return true;
      if (ny >= 0 && board[ny][nx]) return true;
    }
  }
  return false;
}

function rotateCW(shape) {
  const rows = shape.length, cols = shape[0].length;
  const result = Array.from({ length: cols }, () => new Array(rows).fill(0));
  for (let r = 0; r < rows; r++)
    for (let c = 0; c < cols; c++)
      result[c][rows - 1 - r] = shape[r][c];
  return result;
}

function tryRotate() {
  const rotated = rotateCW(current.shape);
  const kicks = [0, -1, 1, -2, 2];
  for (const kick of kicks) {
    if (!collide(rotated, current.x + kick, current.y)) {
      if (current.special) {
        // mismo mapeo que rotateCW: (r, c) -> (c, filas - 1 - r)
        const { r, c } = current.special;
        current.special.r = c;
        current.special.c = current.shape.length - 1 - r;
      }
      current.shape = rotated;
      current.x += kick;
      return;
    }
  }
}

function merge() {
  for (let r = 0; r < current.shape.length; r++)
    for (let c = 0; c < current.shape[r].length; c++)
      if (current.shape[r][c])
        board[current.y + r][current.x + c] = current.shape[r][c];
}

function clearLines() {
  const full = [];
  for (let r = 0; r < ROWS; r++) if (board[r].every(v => v !== 0)) full.push(r);
  const cleared = full.length;
  if (cleared) {
    board = board.filter((_, r) => !full.includes(r));
    while (board.length < ROWS) board.unshift(new Array(COLS).fill(0));
    lines += cleared;
    score += (LINE_SCORES[cleared] || 0) * level;
    level = Math.max(getStartLevel(), Math.floor(lines / 10) + 1);
    dropInterval = Math.max(100, 1000 - (level - 1) * 90);
    fx.push({ kind: 'lines', rows: full, t: 0, dur: 300 });
    // Solo las filas completas cuentan para ganar piezas especiales.
    linesTowardSpecial += cleared;
    while (linesTowardSpecial >= SPECIAL_EVERY_LINES) {
      linesTowardSpecial -= SPECIAL_EVERY_LINES;
      pendingSpecials.push(EFFECT_KEYS[Math.floor(Math.random() * EFFECT_KEYS.length)]);
    }
    updateHUD();
  }
  return cleared;
}

// ---- Efectos especiales (operan sobre `board`, devuelven datos para animar) ----
function effectBomb(cr, cc) {
  const cells = [];
  for (let r = cr - 1; r <= cr + 1; r++)
    for (let c = cc - 1; c <= cc + 1; c++) {
      if (r < 0 || r >= ROWS || c < 0 || c >= COLS) continue;
      if (board[r][c]) { cells.push({ r, c, v: board[r][c] }); board[r][c] = 0; }
    }
  return cells;
}

function effectRay(cr, cc) {
  const cells = [];
  for (let c = 0; c < COLS; c++)
    if (board[cr][c]) { cells.push({ r: cr, c, v: board[cr][c] }); board[cr][c] = 0; }
  for (let r = 0; r < ROWS; r++)
    if (board[r][cc]) { cells.push({ r, c: cc, v: board[r][cc] }); board[r][cc] = 0; }
  return cells;
}

// Convierte en comodines todos los bloques del color `type` (y re-marca los comodines existentes).
function effectTint(type) {
  const cells = [];
  for (let r = 0; r < ROWS; r++)
    for (let c = 0; c < COLS; c++)
      if (board[r][c] === type || board[r][c] === WILD) {
        cells.push({ r, c, v: board[r][c] });
        board[r][c] = WILD;
      }
  return cells;
}

// Cada bloque cae dentro de su columna hasta no dejar huecos; conserva el orden vertical.
function effectGravity() {
  const moves = [];
  for (let c = 0; c < COLS; c++) {
    let write = ROWS - 1;
    for (let r = ROWS - 1; r >= 0; r--) {
      const v = board[r][c];
      if (!v) continue;
      if (r !== write) {
        board[write][c] = v;
        board[r][c] = 0;
        moves.push({ c, from: r, to: write });
      }
      write--;
    }
  }
  return moves;
}

// Activa el efecto de una pieza especial ya fijada. Devuelve true si es Congelar.
function applySpecial(piece) {
  const { effect, r, c } = piece.special;
  const cr = piece.y + r, cc = piece.x + c;
  const label = SPECIAL_EFFECTS[effect];
  fx.push({ kind: 'text', text: `${label.icon} ${label.name}`, t: 0, dur: 900 });
  switch (effect) {
    case 'bomb':
      fx.push({ kind: 'bomb', cr, cc, cells: effectBomb(cr, cc), t: 0, dur: 450 });
      break;
    case 'ray':
      fx.push({ kind: 'ray', cr, cc, cells: effectRay(cr, cc), t: 0, dur: 400 });
      break;
    case 'tint':
      fx.push({ kind: 'tint', cells: effectTint(piece.type), t: 0, dur: 600 });
      break;
    case 'gravity':
      fx.push({ kind: 'gravity', moves: effectGravity(), t: 0, dur: 450 });
      break;
    case 'freeze':
      fx.push({ kind: 'freeze', t: 0, dur: 600 });
      return true;
  }
  return false;
}

function ghostY() {
  let gy = current.y;
  while (!collide(current.shape, current.x, gy + 1)) gy++;
  return gy;
}

function hardDrop() {
  const gy = ghostY();
  score += (gy - current.y) * 2;
  current.y = gy;
  lockPiece();
}

function softDrop() {
  if (!collide(current.shape, current.x, current.y + 1)) {
    current.y++;
    score += 1;
    updateHUD();
  } else {
    lockPiece();
  }
}

function lockPiece() {
  const piece = current;
  freezeMs = 0; // al fijar la pieza congelada, termina el efecto (Congelar la renueva abajo)
  merge();
  const freeze = piece.special ? applySpecial(piece) : false; // una sola vez, al fijarse
  const cleared = clearLines(); // tras cualquier efecto: comprobar filas completas
  runHooks('locked', cleared);
  spawn();
  if (freeze && !gameOver) freezeMs = FREEZE_DURATION_MS;
  updateHUD();
}

function spawn() {
  current = next;
  next = nextPiece();
  if (collide(current.shape, current.x, current.y)) {
    endGame();
  }
  drawNext();
}

function updateHUD() {
  scoreEl.textContent = score.toLocaleString();
  linesEl.textContent = lines;
  levelEl.textContent = level;
  const left = SPECIAL_EVERY_LINES - linesTowardSpecial;
  specialLeftEl.textContent = left === 1 ? 'Falta 1 línea' : `Faltan ${left} líneas`;
  specialQueueEl.textContent = pendingSpecials.length
    ? 'En cola: ' + pendingSpecials.map(k => SPECIAL_EFFECTS[k].icon).join(' ')
    : '';
}

function updateFreezeUI() {
  const text = freezeMs > 0 ? (freezeMs / 1000).toFixed(1) : '';
  if (text === lastFreezeText) return;
  lastFreezeText = text;
  freezeIndicator.classList.toggle('hidden', freezeMs <= 0);
  freezeTimeEl.textContent = text;
}

function drawBlock(context, x, y, colorIndex, size, alpha) {
  if (!colorIndex) return;
  drawCell(context, x, y, colorIndex, size, alpha); // la skin activa decide el aspecto (ver sección Skins)
}

// Dibujo de un bloque con el estilo Retro (por defecto). La unidad de Skins lo sustituye por la skin activa.
function drawCell(context, x, y, colorIndex, size, alpha) {
  context.globalAlpha = alpha === GHOST ? themeVars.ghostAlpha : (alpha ?? 1);
  if (colorIndex === WILD) {
    // comodín: degradado arcoíris con marca ✦
    const g = context.createLinearGradient(x * size, y * size, (x + 1) * size, (y + 1) * size);
    g.addColorStop(0, '#ff8a80');
    g.addColorStop(0.25, '#ffd54f');
    g.addColorStop(0.5, '#81c784');
    g.addColorStop(0.75, '#4dd0e1');
    g.addColorStop(1, '#ba68c8');
    context.fillStyle = g;
  } else {
    context.fillStyle = COLORS[colorIndex];
  }
  context.fillRect(x * size + 1, y * size + 1, size - 2, size - 2);
  // highlight
  context.fillStyle = themeVars.shine;
  context.fillRect(x * size + 1, y * size + 1, size - 2, 4);
  if (colorIndex === WILD) {
    context.fillStyle = 'rgba(255,255,255,0.9)';
    context.font = `${Math.round(size * 0.5)}px sans-serif`;
    context.textAlign = 'center';
    context.textBaseline = 'middle';
    context.fillText('✦', (x + 0.5) * size, (y + 0.5) * size + 1);
  }
  context.globalAlpha = 1;
}

// Dibuja una pieza (normal o especial). (ox, oy) = celda de la esquina superior izquierda de la forma.
function drawPiece(context, piece, ox, oy, size, alpha) {
  const pulse = 0.55 + 0.45 * Math.sin(performance.now() / 180);
  for (let r = 0; r < piece.shape.length; r++)
    for (let c = 0; c < piece.shape[r].length; c++) {
      if (!piece.shape[r][c]) continue;
      drawBlock(context, ox + c, oy + r, piece.shape[r][c], size, alpha);
      if (!piece.special || alpha === GHOST) continue;
      // borde dorado pulsante en todos los bloques especiales
      context.strokeStyle = `rgba(255, 215, 0, ${pulse})`;
      context.lineWidth = 2;
      context.strokeRect((ox + c) * size + 2, (oy + r) * size + 2, size - 4, size - 4);
      if (piece.special.r === r && piece.special.c === c) {
        // núcleo: disco oscuro con el icono del poder (centro del efecto)
        const cx = (ox + c + 0.5) * size, cy = (oy + r + 0.5) * size;
        context.fillStyle = 'rgba(15, 15, 25, 0.8)';
        context.beginPath();
        context.arc(cx, cy, size * 0.36, 0, Math.PI * 2);
        context.fill();
        context.font = `${Math.round(size * 0.46)}px "Segoe UI Emoji","Apple Color Emoji","Noto Color Emoji",sans-serif`;
        context.textAlign = 'center';
        context.textBaseline = 'middle';
        context.fillStyle = '#fff';
        context.fillText(SPECIAL_EFFECTS[piece.special.effect].icon, cx, cy + 1);
      }
    }
}

// ---- Animaciones breves ----
function updateFx(dt) {
  for (const f of fx) f.t += dt;
  fx = fx.filter(f => f.t < f.dur);
}

function fxColor(v) {
  return v === WILD ? '#ffffff' : COLORS[v];
}

function drawFragments(cells, p) {
  const s = BLOCK * (1 - p);
  for (const { r, c, v } of cells) {
    ctx.globalAlpha = 1 - p;
    ctx.fillStyle = fxColor(v);
    ctx.fillRect((c + 0.5) * BLOCK - s / 2, (r + 0.5) * BLOCK - s / 2, s, s);
  }
  ctx.globalAlpha = 1;
}

function drawFx() {
  const W = COLS * BLOCK, H = ROWS * BLOCK;
  ctx.save();
  for (const f of fx) {
    const p = f.t / f.dur;
    switch (f.kind) {
      case 'bomb': {
        drawFragments(f.cells, p);
        const cx = (f.cc + 0.5) * BLOCK, cy = (f.cr + 0.5) * BLOCK;
        const rad = BLOCK * (0.6 + 1.6 * p);
        const g = ctx.createRadialGradient(cx, cy, 0, cx, cy, rad);
        g.addColorStop(0, `rgba(255, 245, 200, ${1 - p})`);
        g.addColorStop(0.5, `rgba(255, 140, 0, ${0.8 * (1 - p)})`);
        g.addColorStop(1, 'rgba(255, 80, 0, 0)');
        ctx.fillStyle = g;
        ctx.fillRect(cx - rad, cy - rad, rad * 2, rad * 2);
        break;
      }
      case 'ray': {
        drawFragments(f.cells, p);
        const th = BLOCK * (1 - p);
        ctx.globalAlpha = 1 - p;
        ctx.fillStyle = '#fff59d';
        ctx.fillRect(0, (f.cr + 0.5) * BLOCK - th / 2, W, th);
        ctx.fillRect((f.cc + 0.5) * BLOCK - th / 2, 0, th, H);
        ctx.fillStyle = '#ffffff';
        ctx.fillRect(0, (f.cr + 0.5) * BLOCK - th / 6, W, th / 3);
        ctx.fillRect((f.cc + 0.5) * BLOCK - th / 6, 0, th / 3, H);
        ctx.globalAlpha = 1;
        break;
      }
      case 'tint': {
        for (const { r, c } of f.cells) {
          const hue = (f.t / 2 + r * 20 + c * 20) % 360;
          ctx.globalAlpha = 0.8 * (1 - p);
          ctx.fillStyle = `hsl(${hue}, 100%, 70%)`;
          ctx.fillRect(c * BLOCK, r * BLOCK, BLOCK, BLOCK);
        }
        ctx.globalAlpha = 1;
        break;
      }
      case 'gravity': {
        for (const { c, from, to } of f.moves) {
          const y0 = from * BLOCK, y1 = (to + 1) * BLOCK;
          const g = ctx.createLinearGradient(0, y0, 0, y1);
          g.addColorStop(0, 'rgba(129, 199, 132, 0)');
          g.addColorStop(1, `rgba(129, 199, 132, ${0.7 * (1 - p)})`);
          ctx.fillStyle = g;
          ctx.fillRect(c * BLOCK + 6, y0, BLOCK - 12, y1 - y0);
        }
        break;
      }
      case 'freeze': {
        ctx.fillStyle = `rgba(140, 210, 255, ${0.35 * (1 - p)})`;
        ctx.fillRect(0, 0, W, H);
        ctx.strokeStyle = `rgba(190, 235, 255, ${1 - p})`;
        ctx.lineWidth = 6;
        ctx.strokeRect(3, 3, W - 6, H - 6);
        break;
      }
      case 'lines': {
        ctx.fillStyle = `rgba(255, 255, 255, ${0.8 * (1 - p)})`;
        for (const r of f.rows) ctx.fillRect(0, r * BLOCK, W, BLOCK);
        break;
      }
      case 'text': {
        ctx.globalAlpha = Math.min(1, 2 * (1 - p));
        ctx.font = 'bold 22px system-ui, sans-serif';
        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';
        ctx.lineWidth = 4;
        ctx.strokeStyle = 'rgba(0,0,0,0.7)';
        const y = 4 * BLOCK - p * BLOCK;
        ctx.strokeText(f.text, W / 2, y);
        ctx.fillStyle = '#ffd700';
        ctx.fillText(f.text, W / 2, y);
        ctx.globalAlpha = 1;
        break;
      }
    }
  }
  ctx.restore();
}

function drawFreezeOverlay() {
  if (freezeMs <= 0) return;
  ctx.save();
  ctx.fillStyle = 'rgba(140, 210, 255, 0.08)';
  ctx.fillRect(0, 0, COLS * BLOCK, ROWS * BLOCK);
  ctx.strokeStyle = 'rgba(140, 210, 255, 0.8)';
  ctx.lineWidth = 3;
  ctx.strokeRect(1.5, 1.5, COLS * BLOCK - 3, ROWS * BLOCK - 3);
  ctx.font = 'bold 18px system-ui, sans-serif';
  ctx.textAlign = 'center';
  ctx.textBaseline = 'top';
  ctx.lineWidth = 3;
  ctx.strokeStyle = 'rgba(0,0,0,0.6)';
  const t = `❄ ${(freezeMs / 1000).toFixed(1)}s`;
  ctx.strokeText(t, COLS * BLOCK / 2, 6);
  ctx.fillStyle = '#b3e5fc';
  ctx.fillText(t, COLS * BLOCK / 2, 6);
  ctx.restore();
}

function drawGrid() {
  ctx.strokeStyle = themeVars.grid;
  ctx.lineWidth = 0.5;
  for (let c = 1; c < COLS; c++) {
    ctx.beginPath();
    ctx.moveTo(c * BLOCK, 0);
    ctx.lineTo(c * BLOCK, ROWS * BLOCK);
    ctx.stroke();
  }
  for (let r = 1; r < ROWS; r++) {
    ctx.beginPath();
    ctx.moveTo(0, r * BLOCK);
    ctx.lineTo(COLS * BLOCK, r * BLOCK);
    ctx.stroke();
  }
}

function draw() {
  ctx.clearRect(0, 0, canvas.width, canvas.height);
  drawGrid();

  // board
  for (let r = 0; r < ROWS; r++)
    for (let c = 0; c < COLS; c++)
      drawBlock(ctx, c, r, board[r][c], BLOCK);

  // ghost
  const gy = ghostY();
  for (let r = 0; r < current.shape.length; r++)
    for (let c = 0; c < current.shape[r].length; c++)
      if (current.shape[r][c])
        drawBlock(ctx, current.x + c, gy + r, current.shape[r][c], BLOCK, GHOST);

  // current piece
  drawPiece(ctx, current, current.x, current.y, BLOCK);

  drawFreezeOverlay();
  drawFx();
  if (next.special) drawNext(); // repinta para animar el borde pulsante
}

function drawNext() {
  const NB = 30;
  nextCtx.clearRect(0, 0, nextCanvas.width, nextCanvas.height);
  const shape = next.shape;
  const offX = Math.floor((4 - shape[0].length) / 2);
  const offY = Math.floor((4 - shape.length) / 2);
  drawPiece(nextCtx, next, offX, offY, NB);
}

function endGame() {
  gameOver = true;
  cancelAnimationFrame(animId);
  overlayTitle.textContent = 'GAME OVER';
  overlayScore.textContent = `Puntuación: ${score.toLocaleString()}`;
  overlay.classList.remove('hidden');
  runHooks('gameOver');
}

function togglePause() {
  if (gameOver) return;
  paused = !paused;
  if (!paused) {
    pauseMenu.classList.add('hidden');
    lastTime = performance.now(); // dt=0 al reanudar: Congelar y animaciones no avanzan en pausa
    loop(lastTime);
  } else {
    cancelAnimationFrame(animId);
    openPauseMenu();
  }
}

function loop(ts) {
  const dt = ts - lastTime;
  lastTime = ts;
  const activeDt = Math.min(dt, 250); // pestaña en segundo plano no consume Congelar/animaciones
  updateFx(activeDt);
  if (freezeMs > 0) {
    freezeMs = Math.max(0, freezeMs - activeDt);
    dropAccum = 0; // sin caída automática mientras dura Congelar
    updateFreezeUI();
  } else {
    dropAccum += dt;
    if (dropAccum >= dropInterval) {
      dropAccum = 0;
      if (!collide(current.shape, current.x, current.y + 1)) {
        current.y++;
      } else {
        lockPiece();
      }
    }
  }
  draw();
  if (gameOver) return;
  animId = requestAnimationFrame(loop);
}

function init() {
  board = createBoard();
  score = 0;
  lines = 0;
  level = getStartLevel();
  paused = false;
  gameOver = false;
  dropInterval = Math.max(100, 1000 - (level - 1) * 90);
  dropAccum = 0;
  lastTime = performance.now();
  // limpiar efectos activos, temporizadores y recompensas pendientes
  pendingSpecials = [];
  linesTowardSpecial = 0;
  freezeMs = 0;
  fx = [];
  lastFreezeText = '';
  freezeIndicator.classList.add('hidden');
  next = randomPiece();
  spawn();
  updateHUD();
  overlay.classList.add('hidden');
  pauseMenu.classList.add('hidden');
  cancelAnimationFrame(animId);
  animId = requestAnimationFrame(loop);
  runHooks('init');
}

document.addEventListener('keydown', e => {
  if (HOOKS.key.some(fn => fn(e))) return;
  if (!started) return;
  if (e.code === 'KeyP' || e.code === 'Escape') { togglePause(); return; }
  if (paused || gameOver) return;
  if (DEBUG && debugKey(e.code)) { updateHUD(); return; }
  switch (e.code) {
    case 'ArrowLeft':
      if (!collide(current.shape, current.x - 1, current.y)) current.x--;
      break;
    case 'ArrowRight':
      if (!collide(current.shape, current.x + 1, current.y)) current.x++;
      break;
    case 'ArrowDown':
      softDrop();
      break;
    case 'ArrowUp':
    case 'KeyX':
      tryRotate();
      break;
    case 'Space':
      e.preventDefault();
      hardDrop();
      break;
  }
  updateHUD();
});

restartBtn.addEventListener('click', init);

// ---- Modo depuración (?debug en la URL) ----
// 1-5: la pieza actual pasa a ser especial (bomba, rayo, tinte, gravedad, congelar)
// 6: encola una recompensa aleatoria · 7: añade 3 filas de basura con un hueco
function debugKey(code) {
  const m = /^Digit([1-7])$/.exec(code);
  if (!m) return false;
  const n = Number(m[1]);
  if (n <= 5) {
    current.special = { effect: EFFECT_KEYS[n - 1], ...coreCell(current.shape) };
  } else if (n === 6) {
    pendingSpecials.push(EFFECT_KEYS[Math.floor(Math.random() * EFFECT_KEYS.length)]);
  } else {
    for (let i = 0; i < 3 && board[0].every(v => v === 0); i++) {
      board.shift();
      const hole = Math.floor(Math.random() * COLS);
      board.push(Array.from({ length: COLS }, (_, c) => (c === hole ? 0 : randomType())));
    }
    if (collide(current.shape, current.x, current.y)) current.y = 0;
  }
  return true;
}
if (DEBUG) debugBadge.classList.remove('hidden');

// ---- Pantalla de inicio ----
let started = false;
const startScreen = document.getElementById('start-screen');
const gameWrapper = document.getElementById('game-wrapper');
const helpBox = document.getElementById('help-box');
const byeMsg = document.getElementById('bye-msg');

document.getElementById('start-btn').addEventListener('click', () => {
  startScreen.classList.add('hidden');
  gameWrapper.classList.remove('hidden');
  started = true;
  init();
});

document.getElementById('help-btn').addEventListener('click', () => {
  byeMsg.classList.add('hidden');
  helpBox.classList.toggle('hidden');
});

document.getElementById('exit-btn').addEventListener('click', () => {
  helpBox.classList.add('hidden');
  window.close(); // solo funciona si la pestaña fue abierta por script
  byeMsg.classList.remove('hidden');
});

// ---- Toggle claro/oscuro (oscuro por defecto) ----
const themeToggle = document.getElementById('theme-toggle');
const themeLabel = document.getElementById('theme-label');

function applyTheme(theme) {
  document.documentElement.dataset.theme = theme;
  const light = theme === 'light';
  themeToggle.setAttribute('aria-checked', String(light));
  themeLabel.textContent = light ? 'CLARO' : 'OSCURO';
  readThemeVars();
  if (started && current && next) { draw(); drawNext(); }
}

themeToggle.addEventListener('click', () => {
  applyTheme(document.documentElement.dataset.theme === 'light' ? 'dark' : 'light');
  themeToggle.blur(); // evita que Space/Enter vuelvan a activar el switch
});

applyTheme('dark');

// ==== [UNIDAD 1] Menú de pausa ====
const pauseMenu = document.getElementById('pause-menu');
const START_LEVEL_KEY = 'tetris.startLevel';
const CONTROLS = [
  ['← →', 'Mover'], ['↓', 'Bajar'], ['↑ / X', 'Rotar'], ['Espacio', 'Caída rápida'], ['P / Esc', 'Pausa'],
];

function getStartLevel() {
  let n = 1;
  try { n = parseInt(localStorage.getItem(START_LEVEL_KEY), 10); } catch (e) { n = 1; }
  return n >= 1 && n <= 10 ? n : 1;
}

function setStartLevel(n) {
  n = Math.min(10, Math.max(1, n));
  try { localStorage.setItem(START_LEVEL_KEY, String(n)); } catch (e) { /* sin almacenamiento */ }
  pmLevelValue.textContent = n;
}

function pmButton(label) {
  const b = document.createElement('button');
  b.type = 'button';
  b.className = 'pm-item';
  b.textContent = label;
  return b;
}

const pmBox = document.createElement('div');
pmBox.className = 'overlay-box pm-box';
const pmTitle = document.createElement('p');
pmTitle.id = 'pm-title';
pmTitle.textContent = 'PAUSA';
const pmResume = pmButton('Reanudar');
const pmRestart = pmButton('Reiniciar');
const pmControlsBtn = pmButton('Ver controles');
const pmControlsList = document.createElement('ul');
pmControlsList.className = 'pm-controls hidden';
CONTROLS.forEach(([k, d]) => {
  const li = document.createElement('li');
  const kbd = document.createElement('kbd');
  kbd.textContent = k;
  li.append(kbd, ' ' + d);
  pmControlsList.appendChild(li);
});
const pmLevelRow = document.createElement('div');
pmLevelRow.className = 'pm-item pm-level';
const pmLevelLabel = document.createElement('span');
pmLevelLabel.textContent = 'Nivel inicial';
const pmLevelDown = document.createElement('button');
pmLevelDown.type = 'button';
pmLevelDown.textContent = '−';
const pmLevelValue = document.createElement('span');
pmLevelValue.className = 'pm-level-value';
const pmLevelUp = document.createElement('button');
pmLevelUp.type = 'button';
pmLevelUp.textContent = '+';
pmLevelRow.append(pmLevelLabel, pmLevelDown, pmLevelValue, pmLevelUp);
pmBox.append(pmTitle, pmResume, pmRestart, pmControlsBtn, pmControlsList, pmLevelRow);
pauseMenu.appendChild(pmBox);

const pmItems = [pmResume, pmRestart, pmControlsBtn, pmLevelRow];
let pmIndex = 0;

function pmSelect(i) {
  pmIndex = (i + pmItems.length) % pmItems.length;
  pmItems.forEach((el, n) => el.classList.toggle('selected', n === pmIndex));
}

function pmRestartGame() { init(); }
function pmToggleControls() { pmControlsList.classList.toggle('hidden'); }
function pmChangeLevel(d) { setStartLevel(getStartLevel() + d); }

function pmActivate(i) {
  if (i === 0) togglePause();
  else if (i === 1) pmRestartGame();
  else if (i === 2) pmToggleControls();
}

function openPauseMenu() {
  pmControlsList.classList.add('hidden');
  pmLevelValue.textContent = getStartLevel();
  pmSelect(0);
  pauseMenu.classList.remove('hidden');
}

pmResume.addEventListener('click', () => pmActivate(0));
pmRestart.addEventListener('click', () => pmActivate(1));
pmControlsBtn.addEventListener('click', () => pmActivate(2));
pmLevelDown.addEventListener('click', () => pmChangeLevel(-1));
pmLevelUp.addEventListener('click', () => pmChangeLevel(1));
pmItems.forEach((el, i) => el.addEventListener('mouseenter', () => pmSelect(i)));

// Teclas mantenidas: tras reanudar, se descartan repeticiones de teclas que no se pulsaron con el juego activo
const pmFreshKeys = new Set();
document.addEventListener('keyup', e => pmFreshKeys.delete(e.code));

HOOKS.key.push(e => {
  const menuOpen = !pauseMenu.classList.contains('hidden');
  if (!menuOpen) {
    if (!e.repeat) pmFreshKeys.add(e.code);
    else if (!pmFreshKeys.has(e.code)) return true;
    return false;
  }
  e.preventDefault();
  if (e.repeat && e.code !== 'ArrowLeft' && e.code !== 'ArrowRight') return true;
  switch (e.code) {
    case 'Escape': case 'KeyP': togglePause(); break;
    case 'ArrowUp': pmSelect(pmIndex - 1); break;
    case 'ArrowDown': pmSelect(pmIndex + 1); break;
    case 'ArrowLeft': if (pmIndex === 3) pmChangeLevel(-1); break;
    case 'ArrowRight': if (pmIndex === 3) pmChangeLevel(1); break;
    case 'Enter': case 'Space': if (pmIndex === 3) pmChangeLevel(1); else pmActivate(pmIndex); break;
  }
  return true;
});

// ==== [UNIDAD 2] Récords ====

// ==== [UNIDAD 3] Skins ====
