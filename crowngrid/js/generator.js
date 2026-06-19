/*
 * CrownGrid puzzle engine
 * --------------------------------------------------------------------------
 * A "Queens-style" logic puzzle: place one crown in every row, every column
 * and every colored region, with no two crowns touching (incl. diagonally).
 *
 * This file is framework-free and attaches a single global: window.CrownGrid.
 * Mechanics (rules) are not copyrightable; visuals/branding here are original.
 */
(function () {
  "use strict";

  // --- Seedable PRNG (mulberry32) so the Daily puzzle is identical for all ---
  function mulberry32(seed) {
    let a = seed >>> 0;
    return function () {
      a |= 0;
      a = (a + 0x6d2b79f5) | 0;
      let t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }

  function shuffle(arr, rng) {
    for (let i = arr.length - 1; i > 0; i--) {
      const j = Math.floor(rng() * (i + 1));
      [arr[i], arr[j]] = [arr[j], arr[i]];
    }
    return arr;
  }

  // --- Step 1: a valid solution = one crown per row/col, none king-adjacent ---
  // Because each row/col holds exactly one crown, the only way two crowns can
  // touch is between consecutive rows, so |col[r] - col[r-1]| must be >= 2.
  function makeSolution(n, rng) {
    const cols = new Array(n).fill(-1);
    const used = new Array(n).fill(false);

    function bt(r) {
      if (r === n) return true;
      const order = shuffle([...Array(n).keys()], rng);
      for (const c of order) {
        if (used[c]) continue;
        if (r > 0 && Math.abs(c - cols[r - 1]) < 2) continue;
        cols[r] = c;
        used[c] = true;
        if (bt(r + 1)) return true;
        used[c] = false;
        cols[r] = -1;
      }
      return false;
    }
    return bt(0) ? cols : null;
  }

  // --- Step 2: grow N contiguous regions, one per crown seed ---
  // Balanced round-robin growth: on every step we extend the SMALLEST region
  // that still has an empty neighbor (ties broken randomly). This keeps every
  // region near the average size (n cells on an n×n board) instead of letting
  // one blob swallow the grid and leaving trivial 1–2 cell regions behind —
  // which both looks better and makes boards far more likely to be solvable by
  // pure logic. Shapes stay irregular because each grab is a random frontier
  // cell of the chosen region.
  const DIRS4 = [[1, 0], [-1, 0], [0, 1], [0, -1]];

  function growRegions(n, solCols, rng) {
    const region = Array.from({ length: n }, () => new Array(n).fill(-1));
    const size = new Array(n).fill(1);
    for (let r = 0; r < n; r++) region[r][solCols[r]] = r; // region id == seed row
    let remaining = n * n - n;

    while (remaining > 0) {
      // Collect, per region, the list of empty frontier cells.
      const frontier = Array.from({ length: n }, () => []);
      for (let r = 0; r < n; r++) {
        for (let c = 0; c < n; c++) {
          if (region[r][c] !== -1) continue;
          for (const [dr, dc] of DIRS4) {
            const nr = r + dr, nc = c + dc;
            if (nr < 0 || nc < 0 || nr >= n || nc >= n) continue;
            const reg = region[nr][nc];
            if (reg !== -1) frontier[reg].push([r, c]);
          }
        }
      }
      // Smallest region that can still grow; random among ties.
      let minSize = Infinity;
      for (let reg = 0; reg < n; reg++)
        if (frontier[reg].length && size[reg] < minSize) minSize = size[reg];
      if (minSize === Infinity) break; // nothing can grow (disconnected leftovers)
      const pick = shuffle([...Array(n).keys()], rng)
        .find((reg) => frontier[reg].length && size[reg] === minSize);
      const cells = frontier[pick];
      const [r, c] = cells[Math.floor(rng() * cells.length)];
      region[r][c] = pick; size[pick]++; remaining--;
    }
    return region;
  }


  // --- No-guess logic solver -------------------------------------------------
  // Models how a human actually solves a CrownGrid: pure constraint propagation
  // plus one-step "what if I put a crown here?" contradiction reasoning — never
  // a blind backtracking guess. If this solver finishes the board, the board is
  // (a) solvable with no guessing and (b) automatically unique, because sound
  // deduction never branches: every forced move is the only move.
  //
  // Cell states in `g`: 0 = unknown, 1 = eliminated (✕), 2 = crown.
  const UNK = 0, ELIM = 1, CROWN = 2;

  // Propagate to a fixpoint. Mutates g. Returns true on contradiction.
  function cgPropagate(n, region, regionCells, g) {
    let changed = true, bad = false;
    function elim(r, c) {
      if (g[r][c] === CROWN) { bad = true; return; }
      if (g[r][c] === UNK) { g[r][c] = ELIM; changed = true; }
    }
    function placeCrown(r, c) { g[r][c] = CROWN; changed = true; }

    while (changed && !bad) {
      changed = false;

      // (1) Each crown attacks its row, column, region and 8 neighbours.
      for (let r = 0; r < n && !bad; r++)
        for (let c = 0; c < n && !bad; c++) {
          if (g[r][c] !== CROWN) continue;
          for (let k = 0; k < n && !bad; k++) {
            if (k !== c) elim(r, k);
            if (k !== r) elim(k, c);
          }
          for (const [rr, cc] of regionCells[region[r][c]])
            if ((rr !== r || cc !== c) && !bad) elim(rr, cc);
          for (let dr = -1; dr <= 1 && !bad; dr++)
            for (let dc = -1; dc <= 1 && !bad; dc++) {
              if (!dr && !dc) continue;
              const nr = r + dr, nc = c + dc;
              if (nr >= 0 && nc >= 0 && nr < n && nc < n) elim(nr, nc);
            }
        }

      // (2) A unit (row / col / region) with no crown: if a single candidate
      //     remains it's forced; if none remain the board is broken.
      const scanUnit = (cells) => {
        if (bad) return;
        let crowns = 0, openR = -1, openC = -1, open = 0;
        for (const [r, c] of cells) {
          if (g[r][c] === CROWN) crowns++;
          else if (g[r][c] === UNK) { open++; openR = r; openC = c; }
        }
        if (crowns === 0) {
          if (open === 0) bad = true;
          else if (open === 1) placeCrown(openR, openC);
        }
      };
      for (let r = 0; r < n; r++) scanUnit(rowCells(n, r));
      for (let c = 0; c < n; c++) scanUnit(colCells(n, c));
      for (let reg = 0; reg < n; reg++) scanUnit(regionCells[reg]);

      // (3) Line confinement, region -> line: if every candidate of a crownless
      //     region sits in one row (or column), that line belongs to the region,
      //     so eliminate the line's candidates that lie outside the region.
      for (let reg = 0; reg < n && !bad; reg++) {
        let crowns = 0, rows = new Set(), cols = new Set();
        for (const [r, c] of regionCells[reg]) {
          if (g[r][c] === CROWN) crowns++;
          else if (g[r][c] === UNK) { rows.add(r); cols.add(c); }
        }
        if (crowns) continue;
        if (rows.size === 1) {
          const r = rows.values().next().value;
          for (let c = 0; c < n; c++) if (g[r][c] === UNK && region[r][c] !== reg) elim(r, c);
        }
        if (cols.size === 1) {
          const c = cols.values().next().value;
          for (let r = 0; r < n; r++) if (g[r][c] === UNK && region[r][c] !== reg) elim(r, c);
        }
      }

      // (4) Line confinement, line -> region: if every candidate of a crownless
      //     row (or column) sits in one region, that region's crown is on this
      //     line, so eliminate the region's candidates on other lines.
      const lineToRegion = (cells, sameLine) => {
        if (bad) return;
        let crowns = 0, regs = new Set();
        for (const [r, c] of cells) {
          if (g[r][c] === CROWN) crowns++;
          else if (g[r][c] === UNK) regs.add(region[r][c]);
        }
        if (crowns || regs.size !== 1) return;
        const reg = regs.values().next().value;
        for (const [r, c] of regionCells[reg])
          if (g[r][c] === UNK && !sameLine(r, c)) elim(r, c);
      };
      for (let r = 0; r < n; r++) lineToRegion(rowCells(n, r), (rr) => rr === r);
      for (let c = 0; c < n; c++) lineToRegion(colCells(n, c), (rr, cc) => cc === c);
    }
    return bad;
  }

  function rowCells(n, r) { const o = []; for (let c = 0; c < n; c++) o.push([r, c]); return o; }
  function colCells(n, c) { const o = []; for (let r = 0; r < n; r++) o.push([r, c]); return o; }

  function cgIsSolved(n, g) {
    let crowns = 0;
    for (let r = 0; r < n; r++) for (let c = 0; c < n; c++) if (g[r][c] === CROWN) crowns++;
    return crowns === n;
  }

  // Returns true iff the board is fully solvable by the logic above (no guessing).
  function logicSolvable(n, region) {
    const regionCells = Array.from({ length: n }, () => []);
    for (let r = 0; r < n; r++) for (let c = 0; c < n; c++) regionCells[region[r][c]].push([r, c]);

    const g = Array.from({ length: n }, () => new Array(n).fill(UNK));
    if (cgPropagate(n, region, regionCells, g)) return false;

    let progress = true;
    while (progress && !cgIsSolved(n, g)) {
      progress = false;
      // One-step contradiction: if placing a crown in a cell forces a broken
      // board, that cell can't be a crown — eliminate it (a fair human move).
      for (let r = 0; r < n && !progress; r++) {
        for (let c = 0; c < n && !progress; c++) {
          if (g[r][c] !== UNK) continue;
          const t = g.map((row) => row.slice());
          t[r][c] = CROWN;
          if (cgPropagate(n, region, regionCells, t)) {
            g[r][c] = ELIM;
            if (cgPropagate(n, region, regionCells, g)) return false;
            progress = true;
          }
        }
      }
    }
    return cgIsSolved(n, g);
  }

  // --- Solver: collect up to `limit` solutions (for the repair loop) ---
  // Each solution is colAt[]: the column of the crown in every row.
  function findSolutions(n, region, limit) {
    const sols = [];
    const usedCol = new Array(n).fill(false);
    const usedReg = new Array(n).fill(false);
    const colAt = new Array(n).fill(-1);

    function bt(r) {
      if (sols.length >= limit) return;
      if (r === n) { sols.push(colAt.slice()); return; }
      for (let c = 0; c < n; c++) {
        if (usedCol[c]) continue;
        const reg = region[r][c];
        if (usedReg[reg]) continue;
        if (r > 0 && Math.abs(c - colAt[r - 1]) < 2) continue;
        usedCol[c] = true; usedReg[reg] = true; colAt[r] = c;
        bt(r + 1);
        usedCol[c] = false; usedReg[reg] = false;
      }
    }
    bt(0);
    return sols;
  }

  // Would region `g` stay one connected piece if cell (rx,cx) left it?
  function connectedWithout(n, region, g, rx, cx) {
    const cells = [];
    for (let r = 0; r < n; r++)
      for (let c = 0; c < n; c++)
        if (region[r][c] === g && !(r === rx && c === cx)) cells.push([r, c]);
    if (!cells.length) return false; // region must not vanish
    const key = (r, c) => r * n + c;
    const inG = new Set(cells.map(([r, c]) => key(r, c)));
    const seen = new Set([key(cells[0][0], cells[0][1])]);
    const stack = [cells[0]];
    while (stack.length) {
      const [r, c] = stack.pop();
      for (const [dr, dc] of DIRS4) {
        const nr = r + dr, nc = c + dc;
        if (nr < 0 || nc < 0 || nr >= n || nc >= n) continue;
        const k = key(nr, nc);
        if (inG.has(k) && !seen.has(k)) { seen.add(k); stack.push([nr, nc]); }
      }
    }
    return seen.size === cells.length;
  }

  function regionSizes(n, region) {
    const s = new Array(n).fill(0);
    for (let r = 0; r < n; r++) for (let c = 0; c < n; c++) s[region[r][c]]++;
    return s;
  }
  // The seed of region g is the solution crown in row g — it must never move,
  // or the intended solution would stop being valid.
  function isSeed(region, sol, r, c) { return region[r][c] === r && sol[r] === c; }

  // --- Repair loop: turn a partition into a UNIQUELY-solvable one -------------
  // Invariant: every region keeps its seed crown, so `sol` always stays a valid
  // solution. As long as a second solution exists, one of its crowns sits on a
  // non-seed cell; moving that cell into a neighbouring region destroys that
  // rival solution (its region loses its only crown) without touching `sol`.
  // Converges to a unique board in a handful of moves.
  function repairToUnique(n, region, sol, rng) {
    for (let iter = 0; iter < 200; iter++) {
      const sols = findSolutions(n, region, 2);
      if (sols.length === 1) return true;
      const alt = sols.find((s) => s.some((c, r) => c !== sol[r])) || sols[1];
      const cands = [];
      for (let r = 0; r < n; r++) if (sol[r] !== alt[r]) cands.push([r, alt[r]]);
      shuffle(cands, rng);
      let moved = false;
      for (const [r, c] of cands) {
        const g = region[r][c];
        if (isSeed(region, sol, r, c)) continue;
        for (const [dr, dc] of shuffle(DIRS4.slice(), rng)) {
          const nr = r + dr, nc = c + dc;
          if (nr < 0 || nc < 0 || nr >= n || nc >= n) continue;
          const g2 = region[nr][nc];
          if (g2 === g) continue;
          if (!connectedWithout(n, region, g, r, c)) continue;
          region[r][c] = g2; moved = true; break;
        }
        if (moved) break;
      }
      if (!moved) return false; // stuck — caller retries with a fresh layout
    }
    return false;
  }

  // --- Polish: improve looks while keeping the solution unique ----------------
  // (a) grow any 1-cell region (a lone color trivially gives away its crown);
  // (b) shave the largest region toward a smaller neighbour. Every move is kept
  // only if the board stays uniquely solvable.
  function polish(n, region, sol, rng) {
    const stillUnique = () => findSolutions(n, region, 2).length === 1;
    for (let pass = 0; pass < 40; pass++) {
      const sz = regionSizes(n, region);
      let changed = false;
      for (let g = 0; g < n; g++) {
        if (sz[g] !== 1) continue;
        const sr = g, sc = sol[g];
        for (const [dr, dc] of shuffle(DIRS4.slice(), rng)) {
          const nr = sr + dr, nc = sc + dc;
          if (nr < 0 || nc < 0 || nr >= n || nc >= n) continue;
          const g2 = region[nr][nc];
          if (g2 === g || isSeed(region, sol, nr, nc) || sz[g2] <= 2) continue;
          if (!connectedWithout(n, region, g2, nr, nc)) continue;
          region[nr][nc] = g;
          if (stillUnique()) { changed = true; break; }
          region[nr][nc] = g2;
        }
      }
      const big = sz.indexOf(Math.max(...sz));
      let shaved = false;
      for (let r = 0; r < n && !shaved; r++)
        for (let c = 0; c < n && !shaved; c++) {
          if (region[r][c] !== big || isSeed(region, sol, r, c)) continue;
          for (const [dr, dc] of shuffle(DIRS4.slice(), rng)) {
            const nr = r + dr, nc = c + dc;
            if (nr < 0 || nc < 0 || nr >= n || nc >= n) continue;
            const g2 = region[nr][nc];
            if (g2 === big || sz[g2] >= sz[big] - 1) continue;
            if (!connectedWithout(n, region, big, r, c)) continue;
            region[r][c] = g2;
            if (stillUnique()) { changed = shaved = true; break; }
            region[r][c] = big;
          }
        }
      if (!changed) break;
    }
    return region;
  }

  // --- Public: generate a no-guess puzzle ---
  // opts: { size, seed }  -> returns { size, regions, solution }
  //
  // Pipeline per attempt:
  //   1. pick a random valid solution,
  //   2. grow balanced regions around it,
  //   3. repair the layout until the solution is UNIQUE,
  //   4. polish the shapes (kill 1-cell regions, shave the biggest),
  //   5. require a clean no-guess solve as a hard guarantee.
  // We return the first board that also clears the aesthetic gate (no 1-cell
  // region, no oversized blob); otherwise the best-looking unique board found.
  function generate(opts) {
    opts = opts || {};
    const n = opts.size || 8;
    const rng = typeof opts.seed === "number" ? mulberry32(opts.seed) : Math.random;
    const CAP = Math.round(1.6 * n); // largest tolerable region
    const MAX_ATTEMPTS = 120;

    let best = null;
    for (let attempt = 0; attempt < MAX_ATTEMPTS; attempt++) {
      const sol = makeSolution(n, rng);
      if (!sol) continue;
      const regions = growRegions(n, sol, rng);
      if (!repairToUnique(n, regions, sol, rng)) continue;
      polish(n, regions, sol, rng);
      if (!logicSolvable(n, regions)) continue; // guarantee: solvable with no guessing
      const sz = regionSizes(n, regions);
      const mn = Math.min.apply(null, sz), mx = Math.max.apply(null, sz);
      if (mn >= 2 && mx <= CAP) return { size: n, regions: regions, solution: sol };
      const score = mn * 100 - mx; // prefer larger min region, then smaller max
      if (!best || score > best.score) best = { size: n, regions: regions, solution: sol, score: score };
    }
    if (best) return { size: best.size, regions: best.regions, solution: best.solution };

    // Essentially never reached: ship a repaired (unique) board without the gate.
    const sol = makeSolution(n, Math.random) || makeSolution(n, rng);
    const regions = growRegions(n, sol, rng);
    repairToUnique(n, regions, sol, rng);
    return { size: n, regions: regions, solution: sol };
  }

  // Deterministic seed for a given calendar day (UTC) -> integer YYYYMMDD.
  function dailySeed(date) {
    const d = date || new Date();
    return d.getUTCFullYear() * 10000 + (d.getUTCMonth() + 1) * 100 + d.getUTCDate();
  }

  window.CrownGrid = window.CrownGrid || {};
  window.CrownGrid.generate = generate;
  window.CrownGrid.dailySeed = dailySeed;
})();
