
class WumpusWorld {
  constructor(rows, cols, pitPct = 0.20) {
    this.rows = rows;
    this.cols = cols;
    this.pitPct = pitPct;
    // grid[r][c] — r=0 is bottom row, r=rows-1 is top row
    this.grid = Array.from({ length: rows }, () =>
      Array.from({ length: cols }, () =>
        ({ pit: false, wumpus: false, gold: false, breeze: false, stench: false })
      )
    );
    this.wumpusPos = null;
    this.goldPos   = null;
    this.pits      = [];
    this._populate();
  }

  _populate() {
    const G = this.grid, R = this.rows, C = this.cols;

    // Place the Wumpus (not at origin)
    let wr, wc;
    do { wr = randInt(R); wc = randInt(C); } while (wr === 0 && wc === 0);
    G[wr][wc].wumpus = true;
    this.wumpusPos = [wr, wc];

    // Place pits randomly (skip origin and Wumpus cell)
    for (let r = 0; r < R; r++) {
      for (let c = 0; c < C; c++) {
        if (r === 0 && c === 0) continue;
        if (r === wr && c === wc) continue;
        if (Math.random() < this.pitPct) {
          G[r][c].pit = true;
          this.pits.push([r, c]);
        }
      }
    }

    // Guarantee at least one pit
    if (this.pits.length === 0) {
      let pr, pc;
      do { pr = randInt(R); pc = randInt(C); }
      while ((pr === 0 && pc === 0) || (pr === wr && pc === wc) || G[pr][pc].pit);
      G[pr][pc].pit = true;
      this.pits.push([pr, pc]);
    }

    // Place gold (not at origin)
    let gr, gc;
    do { gr = randInt(R); gc = randInt(C); } while (gr === 0 && gc === 0);
    G[gr][gc].gold = true;
    this.goldPos = [gr, gc];

    // Propagate breezes and stenches to adjacent cells
    for (let r = 0; r < R; r++) {
      for (let c = 0; c < C; c++) {
        for (const [nr, nc] of this.adj(r, c)) {
          if (G[nr][nc].pit)    G[r][c].breeze = true;
          if (G[nr][nc].wumpus) G[r][c].stench = true;
        }
      }
    }
  }

  // Returns all valid cardinal neighbours of (r, c)
  adj(r, c) {
    const res = [];
    if (r > 0)            res.push([r - 1, c]);
    if (r < this.rows - 1) res.push([r + 1, c]);
    if (c > 0)            res.push([r, c - 1]);
    if (c < this.cols - 1) res.push([r, c + 1]);
    return res;
  }

  // What the agent perceives at (r, c)
  perceive(r, c) {
    const { breeze, stench, gold } = this.grid[r][c];
    return { breeze, stench, glitter: gold };
  }

  isDangerous(r, c) {
    return this.grid[r][c].pit || this.grid[r][c].wumpus;
  }
}


/* ======================================================
   MODULE 2 — KnowledgeBase
   Stores propositional sentences as CNF clauses.
   Each clause is a list of literals (strings).
   Literal naming: "P_r_c" = pit at (r,c), "-P_r_c" = no pit.
   ====================================================== */
class KnowledgeBase {
  constructor() {
    this.clauses = [];        // Array of arrays of literals
    this._keys   = new Set(); // For deduplication
  }

  // Negate a literal: "P_0_1" → "-P_0_1", "-P_0_1" → "P_0_1"
  static neg(lit) {
    return lit.startsWith('-') ? lit.slice(1) : '-' + lit;
  }

  // Unique key for a clause (order-independent)
  static key(clause) {
    return [...clause].sort().join('|');
  }

  // Add a clause; returns true if it was new
  addClause(clause) {
    const uniq = [...new Set(clause)];
    // Skip tautologies (clause contains both p and ¬p)
    for (const lit of uniq) {
      if (uniq.includes(KnowledgeBase.neg(lit))) return false;
    }
    const k = KnowledgeBase.key(uniq);
    if (this._keys.has(k)) return false;
    this._keys.add(k);
    this.clauses.push(uniq);
    return true;
  }

  // Assert a single ground fact
  tell(lit) { return this.addClause([lit]); }

  // Return a deep copy for the resolution engine
  snapshot() { return this.clauses.map(c => [...c]); }
}


/* ======================================================
   MODULE 3 — ResolutionEngine
   Propositional Resolution (proof by contradiction).

   To prove query α:
     1. Negate α and add it to the working clause set
     2. Repeatedly resolve pairs of clauses
     3. If the empty clause is derived → contradiction → α is proven
     4. If no new clauses can be added → α is NOT entailed
   ====================================================== */
class ResolutionEngine {
  constructor() {
    this.totalOps = 0; // Total resolution operations across all asks
    this.lastOps  = 0; // Operations in the most recent ask
  }

  static neg(lit) { return KnowledgeBase.neg(lit); }

  // Resolve c1 and c2 on literal p. Returns resolvent or null.
  static resolveOn(c1, c2, p) {
    const np = ResolutionEngine.neg(p);
    if (!c1.includes(p) || !c2.includes(np)) return null;
    const res = [...new Set([
      ...c1.filter(l => l !== p),
      ...c2.filter(l => l !== np)
    ])];
    // Tautology check
    for (const l of res) {
      if (res.includes(ResolutionEngine.neg(l))) return null;
    }
    return res;
  }

  // Ask: does KB entail `query`? Returns {proved, ops}
  ask(kb, query) {
    const negQ = ResolutionEngine.neg(query);
    const clauses = [...kb.snapshot(), [negQ]];
    const seen    = new Set(clauses.map(c => KnowledgeBase.key(c)));

    const MAX_OPS = 1500;
    let ops = 0, changed = true;

    while (changed && ops < MAX_OPS) {
      changed = false;
      const n = clauses.length;
      for (let i = 0; i < n && ops < MAX_OPS; i++) {
        for (let j = i + 1; j < n && ops < MAX_OPS; j++) {
          for (const lit of clauses[i]) {
            const np = ResolutionEngine.neg(lit);
            if (!clauses[j].includes(np)) continue;

            const resolvent = ResolutionEngine.resolveOn(clauses[i], clauses[j], lit);
            if (resolvent === null) continue;

            ops++;
            this.totalOps++;

            // Empty clause = contradiction = query is proven!
            if (resolvent.length === 0) {
              this.lastOps = ops;
              return { proved: true, ops };
            }

            const k = KnowledgeBase.key(resolvent);
            if (!seen.has(k)) {
              seen.add(k);
              clauses.push(resolvent);
              changed = true;
            }
          }
        }
      }
    }

    this.lastOps = ops;
    return { proved: false, ops };
  }

  // Prove cell (r,c) is safe: no pit AND no wumpus
  askSafe(kb, r, c) {
    return this.ask(kb, `-P_${r}_${c}`).proved &&
           this.ask(kb, `-W_${r}_${c}`).proved;
  }

  // Prove cell (r,c) is dangerous: has pit OR has wumpus
  askDangerous(kb, r, c) {
    const hasPit    = this.ask(kb, `P_${r}_${c}`).proved;
    const hasWumpus = this.ask(kb, `W_${r}_${c}`).proved;
    return { hasPit, hasWumpus, isDangerous: hasPit || hasWumpus };
  }
}


/* ======================================================
   MODULE 4 — Agent
   The knowledge-based agent. Each step it:
     1. Marks its current cell as visited
     2. Perceives (senses breeze, stench, glitter)
     3. TELLs the KB what it learned
     4. ASKs the KB to classify reachable unvisited cells
     5. ACTs by moving to the nearest proven-safe cell
   ====================================================== */
class Agent {
  constructor(world) {
    this.world       = world;
    this.kb          = new KnowledgeBase();
    this.engine      = new ResolutionEngine();

    this.pos         = [0, 0];
    this.visited     = new Set();   // cells the agent has stood on
    this.safeKnown   = new Set();   // cells proven safe by resolution
    this.dangerKnown = new Set();   // cells proven dangerous by resolution
    this.percepts    = {};          // stored percepts per cell key
    this.agentSteps  = 0;
    this.log         = [];          // UI log entries
    this.lastInfer   = [];          // Lines for the inference panel
    this.done        = false;
    this.won         = false;

    // Axiom: the starting cell is always safe
    this.kb.tell('-P_0_0');
    this.kb.tell('-W_0_0');
    this.safeKnown.add('0_0');
    this._log('move', 'Agent starts at (0,0) — safe by definition');
  }

  key(r, c) { return `${r}_${c}`; }

  _log(type, msg) {
    this.log.push({ type, msg });
    if (this.log.length > 300) this.log.shift();
  }

  // TELL: encode percepts as CNF clauses
  tell(percepts) {
    const [r, c]   = this.pos;
    const { breeze, stench } = percepts;
    const nbrs     = this.world.adj(r, c);
    this.lastInfer = [];

    const addFact = (lit, why) => {
      if (this.kb.tell(lit)) {
        const m = `TELL: ${lit} [${why}]`;
        this._log('tell', m);
        this.lastInfer.push(m);
      }
    };

    const addDisj = (lits, why) => {
      if (this.kb.addClause(lits)) {
        const m = `TELL: (${lits.join(' ∨ ')}) [${why}]`;
        this._log('tell', m);
        this.lastInfer.push(m);
      }
    };

    if (!breeze) {
      // No breeze → no pit in any adjacent cell
      for (const [nr, nc] of nbrs) addFact(`-P_${nr}_${nc}`, `no breeze at (${r},${c})`);
    } else {
      // Breeze → pit in at least one adjacent cell (disjunction)
      addDisj(nbrs.map(([nr, nc]) => `P_${nr}_${nc}`), `breeze at (${r},${c})`);
    }

    if (!stench) {
      // No stench → no wumpus in any adjacent cell
      for (const [nr, nc] of nbrs) addFact(`-W_${nr}_${nc}`, `no stench at (${r},${c})`);
    } else {
      // Stench → wumpus in at least one adjacent cell
      addDisj(nbrs.map(([nr, nc]) => `W_${nr}_${nc}`), `stench at (${r},${c})`);
    }
  }

  // ASK: classify reachable unvisited cells via resolution
  ask() {
    const { rows, cols } = this.world;
    for (let r = 0; r < rows; r++) {
      for (let c = 0; c < cols; c++) {
        const k = this.key(r, c);
        if (this.visited.has(k)) continue;

        // Only consider cells reachable from a visited cell
        const reachable = this.world.adj(r, c)
          .some(([nr, nc]) => this.visited.has(this.key(nr, nc)));
        if (!reachable) continue;

        if (!this.safeKnown.has(k) && this.engine.askSafe(this.kb, r, c)) {
          this.safeKnown.add(k);
          const m = `ASK: (${r},${c}) → SAFE (${this.engine.lastOps} ops)`;
          this._log('ask-safe', m);
          this.lastInfer.push(m);
        }

        if (!this.dangerKnown.has(k)) {
          const { isDangerous, hasPit, hasWumpus } = this.engine.askDangerous(this.kb, r, c);
          if (isDangerous) {
            this.dangerKnown.add(k);
            const m = `ASK: (${r},${c}) → DANGER [${hasPit ? 'PIT' : 'WUMPUS'}]`;
            this._log('ask-danger', m);
            this.lastInfer.push(m);
          }
        }
      }
    }
  }

  // Choose the next cell to move to (BFS over safe cells)
  chooseNext() {
    const [cr, cc] = this.pos;

    // Prefer a directly adjacent safe unvisited cell
    for (const [nr, nc] of this.world.adj(cr, cc)) {
      const k = this.key(nr, nc);
      if (this.safeKnown.has(k) && !this.visited.has(k)) return [[nr, nc]];
    }

    // BFS through safe visited cells to find a reachable safe unvisited cell
    const queue = [{ path: [[cr, cc]], pos: [cr, cc] }];
    const seen  = new Set([this.key(cr, cc)]);

    while (queue.length > 0) {
      const { path, pos: [r, c] } = queue.shift();
      for (const [nr, nc] of this.world.adj(r, c)) {
        const k = this.key(nr, nc);
        if (seen.has(k)) continue;
        seen.add(k);
        const np = [...path, [nr, nc]];
        if (this.safeKnown.has(k) && !this.visited.has(k)) return np.slice(1);
        if (this.safeKnown.has(k)) queue.push({ path: np, pos: [nr, nc] });
      }
    }

    return null; // No safe moves reachable
  }

  // STEP: one full Perceive → Tell → Ask → Act cycle
  step() {
    if (this.done) return { status: 'done' };

    const [r, c] = this.pos;
    const k = this.key(r, c);

    this.visited.add(k);
    this.agentSteps++;

    // Death check
    if (this.world.isDangerous(r, c)) {
      this.done = true;
      const { pit } = this.world.grid[r][c];
      const cause = pit ? 'fell into a PIT' : 'eaten by the WUMPUS';
      this._log('death', `☠ DEATH: Agent ${cause} at (${r},${c})!`);
      return { status: 'dead', cause };
    }

    // Gold check
    if (this.world.grid[r][c].gold) {
      this.done = true;
      this.won  = true;
      this._log('gold', `⭐ GOLD found at (${r},${c})! Agent wins!`);
      return { status: 'won' };
    }

    // 1) Perceive
    const percepts = this.world.perceive(r, c);
    this.percepts[k] = percepts;
    const pdesc = [
      percepts.breeze  ? 'Breeze'  : '',
      percepts.stench  ? 'Stench'  : '',
      percepts.glitter ? 'Glitter' : ''
    ].filter(Boolean).join(', ') || 'Nothing';
    this._log('move', `→ Moved to (${r},${c}): sensed ${pdesc}`);

    // 2) Tell
    this.tell(percepts);

    // 3) Ask
    this.ask();

    // 4) Act
    const path = this.chooseNext();
    if (!path || path.length === 0) {
      this.done = true;
      this._log('stuck', '⚠ STUCK: No safe moves left — agent halts');
      return { status: 'stuck' };
    }

    const [nr, nc] = path[0];
    this.pos = [nr, nc];
    this._log('move', `Moving to (${nr},${nc})…`);

    return { status: 'ok', percepts };
  }
}


/* ======================================================
   MODULE 5 — UI
   ====================================================== */
let world    = null;
let agent    = null;
let autoId   = null;   // setInterval handle for auto-mode
let revealed = false;

// Start a brand-new game
function initGame() {
  stopAuto();
  revealed = false;

  const rows   = clamp(parseInt(document.getElementById('cfg-rows').value) || 4, 3, 7);
  const cols   = clamp(parseInt(document.getElementById('cfg-cols').value) || 4, 3, 7);
  const pitPct = clamp(parseInt(document.getElementById('cfg-pit').value)  || 20, 5, 45) / 100;

  world = new WumpusWorld(rows, cols, pitPct);
  agent = new Agent(world);

  document.getElementById('btn-step').disabled   = false;
  document.getElementById('btn-auto').disabled   = false;
  document.getElementById('btn-reveal').disabled = false;
  document.getElementById('btn-reveal').textContent = '👁 Reveal';
  document.getElementById('log').innerHTML   = '';
  document.getElementById('infer').innerHTML = '<span style="color:#bbb">Awaiting first step…</span>';

  setStatus('World ready — agent at (0,0)');
  renderAll();
  doStep(); // Run first step automatically to sense the start cell
}

// Execute one agent step
function doStep() {
  if (!agent || agent.done) return;

  const result = agent.step();
  renderAll();

  if (result.status === 'dead') {
    stopAuto();
    revealed = true;
    renderAll();
    disableCtrl();
    showModal('💀', 'Agent Died',
      `The agent ${result.cause} at step ${agent.agentSteps}. ` +
      `Used ${agent.engine.totalOps} inference operations.`);

  } else if (result.status === 'won') {
    stopAuto();
    revealed = true;
    renderAll();
    disableCtrl();
    showModal('⭐', 'Gold Found!',
      `Agent found the gold in ${agent.agentSteps} steps with ` +
      `${agent.engine.totalOps} inference operations.`);

  } else if (result.status === 'stuck') {
    stopAuto();
    disableCtrl();
    showModal('🤔', 'Agent Stuck',
      `No proven-safe moves remain. Explored ${agent.visited.size} of ` +
      `${world.rows * world.cols} cells.`);
  }
}

// Toggle auto-stepping on/off
function toggleAuto() {
  if (autoId) {
    stopAuto();
    setStatus('Paused');
  } else {
    const delay = parseInt(document.getElementById('speed').value);
    document.getElementById('btn-auto').textContent = '⏸ Pause';
    setStatus('Auto-running…');
    autoId = setInterval(() => {
      if (!agent || agent.done) { stopAuto(); return; }
      doStep();
    }, delay);
  }
}

function stopAuto() {
  if (autoId) { clearInterval(autoId); autoId = null; }
  document.getElementById('btn-auto').textContent = '▶▶ Auto';
}

// Toggle world reveal
function toggleReveal() {
  revealed = !revealed;
  document.getElementById('btn-reveal').textContent = revealed ? '🙈 Hide' : '👁 Reveal';
  renderGrid();
}

// Speed slider changed
function onSpeedChange() {
  const v = document.getElementById('speed').value;
  document.getElementById('spd-lbl').textContent = v + 'ms';
  if (autoId) { stopAuto(); toggleAuto(); } // restart with new speed
}

// Render both grid and dashboard
function renderAll() { renderGrid(); renderDash(); }

// Render the cave grid
function renderGrid() {
  if (!world || !agent) return;
  const { rows, cols } = world;
  const gridEl = document.getElementById('grid');
  gridEl.style.gridTemplateColumns = `repeat(${cols}, 82px)`;

  let html = '';
  // r=0 is bottom row so we render top-to-bottom visually (rows-1 → 0)
  for (let r = rows - 1; r >= 0; r--) {
    for (let c = 0; c < cols; c++) {
      const k       = `${r}_${c}`;
      const isAgent = agent.pos[0] === r && agent.pos[1] === c;
      const visited = agent.visited.has(k);
      const safe    = agent.safeKnown.has(k);
      const danger  = agent.dangerKnown.has(k);
      const perc    = agent.percepts[k];

      // CSS class for background colour
      let cls = 'cell';
      if (isAgent)       cls += ' current';
      else if (danger)   cls += ' danger';
      else if (visited)  cls += ' visited';
      else if (safe)     cls += ' safe';

      // Icon (agent / revealed contents)
      let icon = '';
      if (isAgent) {
        icon = '🧭';
      } else if (revealed) {
        const cell = world.grid[r][c];
        if (cell.wumpus)    icon = '👹';
        else if (cell.pit)  icon = '🕳';
        else if (cell.gold) icon = '⭐';
      }

      // Label for unvisited cells
      let tag = '';
      if (!isAgent && !visited) {
        if (danger)     tag = '<div class="cell-tag danger-tag">DANGER</div>';
        else if (safe)  tag = '<div class="cell-tag safe-tag">SAFE</div>';
        else            tag = '<div class="cell-tag unknown-tag">?</div>';
      }

      // Percept badges for visited cells
      let badges = '';
      if (perc && visited) {
        let b = '';
        if (perc.breeze)  b += '<span class="badge badge-B">B</span>';
        if (perc.stench)  b += '<span class="badge badge-S">S</span>';
        if (perc.glitter) b += '<span class="badge badge-G">G</span>';
        if (b) badges = `<div class="badges">${b}</div>`;
      }

      html += `<div class="${cls}">
        <div class="cell-coord">${r},${c}</div>
        ${icon ? `<div class="cell-icon">${icon}</div>` : ''}
        ${badges}${tag}
      </div>`;
    }
  }
  gridEl.innerHTML = html;
}

// Render the right-hand dashboard
function renderDash() {
  if (!agent) return;
  const [r, c] = agent.pos;

  // Stats
  document.getElementById('s-steps').textContent  = agent.agentSteps;
  document.getElementById('s-infer').textContent  = agent.engine.totalOps;
  document.getElementById('s-safe').textContent   = agent.safeKnown.size;
  document.getElementById('s-danger').textContent = agent.dangerKnown.size;

  // Position
  document.getElementById('cur-pos').textContent = `(${r},${c})`;

  // Percept pills
  const p = agent.percepts[agent.key(r, c)] || {};
  const setPill = (id, on, cls) => {
    document.getElementById(id).className = `pill${on ? ' ' + cls : ''}`;
  };
  setPill('pp-B', p.breeze,  'on-B');
  setPill('pp-S', p.stench,  'on-S');
  setPill('pp-G', p.glitter, 'on-G');

  // Inference panel (last 4 lines)
  const inferEl = document.getElementById('infer');
  if (agent.lastInfer.length > 0) {
    inferEl.innerHTML = agent.lastInfer.slice(-4)
      .map(m => `<div class="infer-line">${esc(m)}</div>`)
      .join('');
  }

  // KB log (last 60 entries, newest at bottom)
  const logEl  = document.getElementById('log');
  const typeMap = {
    tell:       'log-tell',
    'ask-safe': 'log-safe',
    'ask-danger':'log-danger',
    move:       'log-move',
    death:      'log-death',
    gold:       'log-gold',
    stuck:      'log-stuck'
  };
  logEl.innerHTML = agent.log.slice(-60)
    .map(e => `<div class="${typeMap[e.type] || 'log-move'}">${esc(e.msg)}</div>`)
    .join('');
  logEl.scrollTop = logEl.scrollHeight;

  setStatus(`Step ${agent.agentSteps} | Agent at (${r},${c}) | KB: ${agent.kb.clauses.length} clauses`);
}

// ── Helpers ──
function setStatus(m) { document.getElementById('status-txt').textContent = m; }

function showModal(icon, title, msg) {
  document.getElementById('m-icon').textContent  = icon;
  document.getElementById('m-title').textContent = title;
  document.getElementById('m-msg').textContent   = msg;
  document.getElementById('modal').classList.add('show');
}

function closeModal() { document.getElementById('modal').classList.remove('show'); }

function disableCtrl() {
  document.getElementById('btn-step').disabled = true;
  document.getElementById('btn-auto').disabled = true;
}

function esc(s) {
  return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

function randInt(n)       { return Math.floor(Math.random() * n); }
function clamp(v, lo, hi) { return Math.max(lo, Math.min(hi, v)); }

// ── Event wiring ──
document.getElementById('modal').addEventListener('click', e => {
  if (e.target === document.getElementById('modal')) closeModal();
});

window.addEventListener('resize', () => { if (world) renderGrid(); });

// ── Boot ──
initGame();
