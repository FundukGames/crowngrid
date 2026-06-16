/*
 * SunMoon puzzle engine (binary-logic / "Tango"-style).
 * --------------------------------------------------------------------------
 * Fill an N×N grid with ☀ (0) and 🌙 (1) so that:
 *   - no three identical symbols are adjacent in a row or column,
 *   - each row and each column has equal numbers of ☀ and 🌙 (N/2 each),
 *   - "=" / "✕" edge clues between neighbors are satisfied (same / different).
 * Every generated board has exactly one logical solution.
 *
 * Framework-free; attaches window.SunMoon. Mechanics (rules) are not
 * copyrightable; the name and visuals here are original.
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

  // --- Count solutions (up to `limit`) for givens + edge clues ------------
  // givens: n×n, -1 unknown else 0/1.  h[r][c]: clue between (r,c)&(r,c+1).
  // v[r][c]: clue between (r,c)&(r+1,c).  clue: 0 none, 1 equal, 2 different.
  function countSolutions(n, givens, h, v, limit) {
    const half = n / 2;
    // Fill row-major from empty; givens are forced values, validated incrementally
    // against already-placed cells (so counts are never double-counted).
    const grid = Array.from({ length: n }, () => new Array(n).fill(-1));
    const rowCnt = Array.from({ length: n }, () => [0, 0]);
    const colCnt = Array.from({ length: n }, () => [0, 0]);

    let count = 0;
    function ok(r, c, val) {
      if (rowCnt[r][val] === half) return false;
      if (colCnt[c][val] === half) return false;
      if (c >= 2 && grid[r][c - 1] === val && grid[r][c - 2] === val) return false;
      if (r >= 2 && grid[r - 1][c] === val && grid[r - 2][c] === val) return false;
      if (c >= 1 && h[r][c - 1] && grid[r][c - 1] !== -1) {
        const same = grid[r][c - 1] === val;
        if (h[r][c - 1] === 1 && !same) return false;
        if (h[r][c - 1] === 2 && same) return false;
      }
      if (r >= 1 && v[r - 1][c] && grid[r - 1][c] !== -1) {
        const same = grid[r - 1][c] === val;
        if (v[r - 1][c] === 1 && !same) return false;
        if (v[r - 1][c] === 2 && same) return false;
      }
      return true;
    }
    function bt(idx) {
      if (count >= limit) return;
      if (idx === n * n) { count++; return; }
      const r = (idx / n) | 0, c = idx % n;
      const g = givens[r][c];
      if (g !== -1) {
        if (ok(r, c, g)) { grid[r][c] = g; rowCnt[r][g]++; colCnt[c][g]++; bt(idx + 1); grid[r][c] = -1; rowCnt[r][g]--; colCnt[c][g]--; }
        return;
      }
      for (let val = 0; val <= 1; val++) {
        if (!ok(r, c, val)) continue;
        grid[r][c] = val; rowCnt[r][val]++; colCnt[c][val]++;
        bt(idx + 1);
        grid[r][c] = -1; rowCnt[r][val]--; colCnt[c][val]--;
      }
    }
    bt(0);
    return count;
  }

  // --- Generate a uniquely solvable puzzle --------------------------------
  function generate(opts) {
    opts = opts || {};
    const n = (opts.size || 6) & ~1; // force even
    const rng = typeof opts.seed === "number" ? mulberry32(opts.seed) : Math.random;

    let sol = null;
    for (let i = 0; i < 50 && !sol; i++) sol = makeSolution(n, rng);
    if (!sol) sol = makeSolution(n, Math.random);

    // Start fully constrained (all givens + all edges) -> trivially unique.
    const givens = sol.map((row) => row.slice());
    const h = Array.from({ length: n }, () => new Array(n).fill(0));
    const v = Array.from({ length: n }, () => new Array(n).fill(0));
    for (let r = 0; r < n; r++)
      for (let c = 0; c < n; c++) {
        if (c < n - 1) h[r][c] = sol[r][c] === sol[r][c + 1] ? 1 : 2;
        if (r < n - 1) v[r][c] = sol[r][c] === sol[r + 1][c] ? 1 : 2;
      }

    // Build a removal order: givens first (shuffled), then edges (shuffled),
    // so the final puzzle keeps few givens and several =/✕ clues (authentic).
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

      if (countSolutions(n, givens, h, v, 2) !== 1) {
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
