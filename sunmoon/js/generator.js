/*
 * SunMoon puzzle engine (binary-logic / "Tango"-style).
 * --------------------------------------------------------------------------
 * Fill an N×N grid with ☀ (0) and 🌙 (1) so that:
 *   - no three identical symbols are adjacent in a row or column,
 *   - each row and each column has equal numbers of ☀ and 🌙 (N/2 each),
 *   - "=" / "✕" edge clues between neighbors are satisfied (same / different).
 *
 * Every generated board is solvable by PURE LOGIC (constraint propagation) —
 * no guessing — which also makes the solution unique. Framework-free; attaches
 * window.SunMoon. Mechanics (rules) are not copyrightable; name/visuals original.
 */
(function () {
  "use strict";

  function mulberry32(seed) {
    let a = seed >>> 0;
    return function () {
      a |= 0; a = (a + 0x6d2b79f5) | 0;
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

  // --- A full valid solution: balanced rows/cols, no 3-in-a-row -----------
  function makeSolution(n, rng) {
    const half = n / 2;
    const grid = Array.from({ length: n }, () => new Array(n).fill(-1));
    const rowCnt = Array.from({ length: n }, () => [0, 0]);
    const colCnt = Array.from({ length: n }, () => [0, 0]);
    function bt(idx) {
      if (idx === n * n) return true;
      const r = (idx / n) | 0, c = idx % n;
      for (const v of shuffle([0, 1], rng)) {
        if (rowCnt[r][v] === half) continue;
        if (colCnt[c][v] === half) continue;
        if (c >= 2 && grid[r][c - 1] === v && grid[r][c - 2] === v) continue;
        if (r >= 2 && grid[r - 1][c] === v && grid[r - 2][c] === v) continue;
        grid[r][c] = v; rowCnt[r][v]++; colCnt[c][v]++;
        if (bt(idx + 1)) return true;
        grid[r][c] = -1; rowCnt[r][v]--; colCnt[c][v]--;
      }
      return false;
    }
    return bt(0) ? grid : null;
  }

  // --- Logic solver: fill only FORCED cells via constraint propagation -----
  // Returns { grid, solved, contradiction }. "solved" means pure deduction
  // (no guessing) filled the whole board.
  function logicSolve(n, givens, h, v) {
    const half = n / 2;
    const g = givens.map((row) => row.slice());
    let contradiction = false, changed = true;

    function set(r, c, val) {
      if (g[r][c] === val) return;
      if (g[r][c] !== -1) { contradiction = true; return; }
      g[r][c] = val; changed = true;
    }

    while (changed && !contradiction) {
      changed = false;

      // Balance: a line that already has N/2 of one symbol forces the rest.
      for (let r = 0; r < n && !contradiction; r++) {
        let z = 0, o = 0;
        for (let c = 0; c < n; c++) { if (g[r][c] === 0) z++; else if (g[r][c] === 1) o++; }
        if (z > half || o > half) contradiction = true;
        else if (z === half) for (let c = 0; c < n; c++) if (g[r][c] === -1) set(r, c, 1);
        else if (o === half) for (let c = 0; c < n; c++) if (g[r][c] === -1) set(r, c, 0);
      }
      for (let c = 0; c < n && !contradiction; c++) {
        let z = 0, o = 0;
        for (let r = 0; r < n; r++) { if (g[r][c] === 0) z++; else if (g[r][c] === 1) o++; }
        if (z > half || o > half) contradiction = true;
        else if (z === half) for (let r = 0; r < n; r++) if (g[r][c] === -1) set(r, c, 1);
        else if (o === half) for (let r = 0; r < n; r++) if (g[r][c] === -1) set(r, c, 0);
      }

      // No-three: in any run of 3, two equal knowns force the third opposite.
      const triple = (a, b, cc) => {
        // a,b,cc are [r,c] cells of three consecutive
        const va = g[a[0]][a[1]], vb = g[b[0]][b[1]], vc = g[cc[0]][cc[1]];
        if (va !== -1 && va === vb && vc === -1) set(cc[0], cc[1], 1 - va);       // A A _
        else if (vb !== -1 && vb === vc && va === -1) set(a[0], a[1], 1 - vb);    // _ A A
        else if (va !== -1 && va === vc && vb === -1) set(b[0], b[1], 1 - va);    // A _ A
      };
      for (let r = 0; r < n; r++) for (let c = 0; c + 2 < n; c++) triple([r, c], [r, c + 1], [r, c + 2]);
      for (let c = 0; c < n; c++) for (let r = 0; r + 2 < n; r++) triple([r, c], [r + 1, c], [r + 2, c]);

      // Edge clues: a known endpoint forces its partner.
      for (let r = 0; r < n; r++) {
        for (let c = 0; c < n; c++) {
          if (c < n - 1 && h[r][c]) {
            const a = g[r][c], b = g[r][c + 1], same = h[r][c] === 1;
            if (a !== -1 && b === -1) set(r, c + 1, same ? a : 1 - a);
            else if (b !== -1 && a === -1) set(r, c, same ? b : 1 - b);
          }
          if (r < n - 1 && v[r][c]) {
            const a = g[r][c], b = g[r + 1][c], same = v[r][c] === 1;
            if (a !== -1 && b === -1) set(r + 1, c, same ? a : 1 - a);
            else if (b !== -1 && a === -1) set(r, c, same ? b : 1 - b);
          }
        }
      }
    }

    let solved = !contradiction;
    for (let r = 0; r < n && solved; r++) for (let c = 0; c < n; c++) if (g[r][c] === -1) { solved = false; break; }
    return { grid: g, solved: solved, contradiction: contradiction };
  }

  // --- Generate a puzzle solvable by pure logic (hence unique) ------------
  function generate(opts) {
    opts = opts || {};
    const n = (opts.size || 6) & ~1; // even
    const rng = typeof opts.seed === "number" ? mulberry32(opts.seed) : Math.random;

    let sol = null;
    for (let i = 0; i < 60 && !sol; i++) sol = makeSolution(n, rng);
    if (!sol) sol = makeSolution(n, Math.random);

    // Start fully constrained (all givens + all edges) — trivially solvable.
    const givens = sol.map((row) => row.slice());
    const h = Array.from({ length: n }, () => new Array(n).fill(0));
    const v = Array.from({ length: n }, () => new Array(n).fill(0));
    for (let r = 0; r < n; r++)
      for (let c = 0; c < n; c++) {
        if (c < n - 1) h[r][c] = sol[r][c] === sol[r][c + 1] ? 1 : 2;
        if (r < n - 1) v[r][c] = sol[r][c] === sol[r + 1][c] ? 1 : 2;
      }

    // Remove clues (givens first, then edges) while the board still solves by
    // pure logic. Keeping logic-solvability guarantees a single, deducible path.
    const givenHandles = [];
    for (let r = 0; r < n; r++) for (let c = 0; c < n; c++) givenHandles.push(["g", r, c]);
    const edgeHandles = [];
    for (let r = 0; r < n; r++)
      for (let c = 0; c < n; c++) {
        if (c < n - 1) edgeHandles.push(["h", r, c]);
        if (r < n - 1) edgeHandles.push(["v", r, c]);
      }
    const order = shuffle(givenHandles, rng).concat(shuffle(edgeHandles, rng));

    for (const [type, r, c] of order) {
      let prev;
      if (type === "g") { prev = givens[r][c]; givens[r][c] = -1; }
      else if (type === "h") { prev = h[r][c]; h[r][c] = 0; }
      else { prev = v[r][c]; v[r][c] = 0; }

      if (!logicSolve(n, givens, h, v).solved) {
        if (type === "g") givens[r][c] = prev;
        else if (type === "h") h[r][c] = prev;
        else v[r][c] = prev;
      }
    }

    return { size: n, solution: sol, givens: givens, h: h, v: v };
  }

  function dailySeed(date) {
    const d = date || new Date();
    return d.getUTCFullYear() * 10000 + (d.getUTCMonth() + 1) * 100 + d.getUTCDate();
  }

  window.SunMoon = window.SunMoon || {};
  window.SunMoon.generate = generate;
  window.SunMoon.dailySeed = dailySeed;
})();
