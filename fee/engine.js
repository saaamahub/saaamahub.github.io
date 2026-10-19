/* SAAAMA fee proposal layout engine.
   One layout -> two renderers (HTML preview + vector PDF) so both are identical.
   Units: Canva px (A4 = 793.7 x 1122.5). PDF pt = px * 0.75. */
(function (global) {
  'use strict';

  var W = 793.7007874, H = 1122.519685;
  var GREEN = '#3b5e45', CREAM = '#f3f1ea', INK = '#111111', BLACK = '#000000';

  // weight/style -> font key
  function fkey(w, i) {
    var base = w === 300 ? 'L' : w === 500 ? 'M' : w === 700 ? 'B' : 'R';
    return base + (i ? 'I' : '');
  }
  var FONT_FILES = { L: 'Light', LI: 'LightItalic', R: 'Regular', RI: 'Italic', M: 'Medium', B: 'Bold', BI: 'BoldItalic' };

  var E = {
    fonts: {},          // key -> opentype.Font
    fontB64: {},        // key -> base64 ttf
    images: {},         // key -> dataURL
    // calibrated baseline offsets: baseline = top + k*fs  (keyed by line-height)
    BASE: { '1.1': 0.965, '1.4': 0.93, '1.78': 0.85 },
    // first-line box height factor (element height of a single line = h1*fs)
    H1: { '1.1': 1.18, '1.4': 1.133, '1.78': 1.145 },
    LIST: { indents: [0, 24.0, 45.5, 68.6], markerGap: 2.5, discCenterFromText: 13.3, discR: 2.15, discLift: 0.33 },
    W: W, H: H
  };

  E.init = function (fontB64, images) {
    E.fontB64 = fontB64; E.images = images || {};
    var ps = [];
    Object.keys(fontB64).forEach(function (k) {
      var buf = b64ToBuf(fontB64[k]);
      E.fonts[k] = opentype.parse(buf);
      if (typeof FontFace !== 'undefined') {
        var w = k[0] === 'L' ? 300 : k[0] === 'M' ? 500 : k[0] === 'B' ? 700 : 400;
        var ff = new FontFace('SaaamaSans', buf, { weight: String(w), style: k.indexOf('I') > 0 ? 'italic' : 'normal' });
        ps.push(ff.load().then(function (f) { document.fonts.add(f); }));
      }
    });
    return Promise.all(ps);
  };

  function b64ToBuf(b64) {
    var bin = atob(b64), n = bin.length, u = new Uint8Array(n);
    for (var i = 0; i < n; i++) u[i] = bin.charCodeAt(i);
    return u.buffer;
  }

  // ---------- measuring ----------
  var kernCache = {};
  function glyphRun(font, text) { return font.stringToGlyphs(text); }
  function kern(font, a, b) {
    try { return font.getKerningValue(a, b) || 0; } catch (e) { return 0; }
  }
  // returns {width, segs:[{t, dx}]} where segs split on non-zero kerning (for PDF)
  function measure(text, fk, fs, ls) {
    var font = E.fonts[fk];
    var scale = fs / font.unitsPerEm;
    var glyphs = glyphRun(font, text);
    var x = 0, segs = [], cur = '', curX = 0;
    var chars = Array.from(text);
    for (var i = 0; i < glyphs.length; i++) {
      var g = glyphs[i];
      if (i > 0) {
        var kv = kern(font, glyphs[i - 1], g) * scale;
        if (kv !== 0) {
          segs.push({ t: cur, dx: curX }); cur = ''; x += kv; curX = x;
        }
      }
      cur += chars[i] !== undefined ? chars[i] : '';
      x += (g.advanceWidth || 0) * scale + ls;
    }
    if (cur) segs.push({ t: cur, dx: curX });
    return { width: x, segs: segs };
  }
  E.measure = measure;

  // ---------- text model ----------
  // run: {t, w(weight), i(italic), c(color), u(underline), sup}
  function R(t, w, o) { o = o || {}; return { t: t, w: w || 300, i: !!o.i, c: o.c, u: !!o.u, sup: !!o.sup }; }
  E.R = R;

  // parse light markup: **bold**, _italic_
  function md(str, baseW, color) {
    var out = [], re = /(\*\*[^*]+\*\*|_[^_]+_)/g, last = 0, m;
    str = String(str || '');
    while ((m = re.exec(str))) {
      if (m.index > last) out.push(R(str.slice(last, m.index), baseW, { c: color }));
      var tok = m[0];
      if (tok[0] === '*') out.push(R(tok.slice(2, -2), 700, { c: color }));
      else out.push(R(tok.slice(1, -1), baseW, { i: true, c: color }));
      last = m.index + tok.length;
    }
    if (last < str.length) out.push(R(str.slice(last), baseW, { c: color }));
    return out;
  }
  E.md = md;

  // split "m²" into sup runs (font lacks U+00B2)
  function expandSup(runs) {
    var out = [];
    runs.forEach(function (r) {
      var parts = r.t.split('²');
      parts.forEach(function (p, idx) {
        if (p) out.push(Object.assign({}, r, { t: p }));
        if (idx < parts.length - 1) out.push(Object.assign({}, r, { t: '2', sup: true }));
      });
    });
    return out;
  }

  function runSize(r, fs) { return r.sup ? fs * 0.62 : fs; }

  // tokenise runs into breakable pieces; break after space, '/', '-'
  function tokens(runs) {
    var toks = [];
    runs.forEach(function (r) {
      var re = /[^\s\/\-]*[\/\-]?\s*/g, m;
      var s = r.t;
      while ((m = re.exec(s)) && m[0].length) {
        toks.push(Object.assign({}, r, { t: m[0] }));
        if (re.lastIndex >= s.length) break;
      }
    });
    return toks;
  }

  // layout one paragraph (runs) into lines within width; returns [{runs:[{..., x}] , width}]
  function wrapPara(runs, width, fs, ls, firstIndent) {
    var lines = [], cur = [], curW = 0;
    var toks = tokens(expandSup(runs));
    function push() { lines.push(cur); cur = []; curW = 0; }
    toks.forEach(function (tk) {
      var sz = runSize(tk, fs);
      var full = measure(tk.t, fkey(tk.w, tk.i), sz, ls * (sz / fs)).width;
      var trimmed = measure(tk.t.replace(/\s+$/, ''), fkey(tk.w, tk.i), sz, ls * (sz / fs)).width;
      var avail = width - (lines.length === 0 ? (firstIndent || 0) : 0);
      if (cur.length && curW + trimmed > avail + 0.01 && !/^\s*$/.test(tk.t)) push();
      cur.push(tk); curW += full;
    });
    if (cur.length || !lines.length) push();
    // merge adjacent tokens with same style
    return lines.map(function (ln) {
      var merged = [];
      ln.forEach(function (tk) {
        var p = merged[merged.length - 1];
        if (p && p.w === tk.w && p.i === tk.i && p.c === tk.c && p.u === tk.u && p.sup === tk.sup) p.t += tk.t;
        else merged.push(Object.assign({}, tk));
      });
      return merged;
    });
  }

  function romanize(n) {
    var r = '', map = [[10, 'x'], [9, 'ix'], [5, 'v'], [4, 'iv'], [1, 'i']];
    map.forEach(function (p) { while (n >= p[0]) { r += p[1]; n -= p[0]; } });
    return r;
  }

  /* text block.
     spec: {x, top, width, fs, lh, ls(em), color, align('start'|'center'|'end'), paras:[ {runs, list:{type, level, n}, blank:true} ]}
     returns {items:[], lines:[{top, baseline, firstOfPara, paraIndex}], height, nLines} */
  function block(spec) {
    var fs = spec.fs, lh = spec.lh, adv = Math.floor(fs * lh + 1e-9);
    var lsPx = (spec.ls || 0) * fs;
    var kB = E.BASE[String(lh)], h1 = E.H1[String(lh)] * fs;
    var items = [], lineInfo = [], li = 0;
    spec.paras.forEach(function (p, pi) {
      if (p.blank) { lineInfo.push({ paraIndex: pi, blank: true, baseline: spec.top + kB * fs + li * adv }); li++; return; }
      var list = p.list, textX = spec.x, markerRuns = null;
      if (list) {
        textX = spec.x + E.LIST.indents[list.level] * (fs / 13.3334);
      }
      var runs = p.runs.map(function (r) { return Object.assign({ c: spec.color || INK }, r, { c: r.c || spec.color || INK }); });
      var lines = wrapPara(runs, spec.width - (textX - spec.x), fs, lsPx, 0);
      lines.forEach(function (ln, k) {
        var baseline = spec.top + kB * fs + li * adv;
        var lw = 0;
        var placed = ln.map(function (r) {
          var sz = runSize(r, fs);
          var m = measure(r.t, fkey(r.w, r.i), sz, lsPx * (sz / fs));
          var o = Object.assign({}, r, { x: lw, size: sz, segs: m.segs, width: m.width, ls: lsPx * (sz / fs) });
          lw += m.width; return o;
        });
        var x0 = textX;
        if (spec.align === 'center') { var tw = lw - trailingSpaceW(placed, fs, lsPx); x0 = spec.x + (spec.width - tw) / 2; }
        if (spec.align === 'end') { var tw2 = lw - trailingSpaceW(placed, fs, lsPx); x0 = spec.x + spec.width - tw2; }
        placed.forEach(function (r) {
          var y = baseline - (r.sup ? fs * 0.36 : 0);
          items.push({ type: 'text', x: x0 + r.x, y: y, t: r.t, fk: fkey(r.w, r.i), size: r.size, color: r.c, ls: r.ls, segs: r.segs, width: r.width, u: r.u, w: r.w, i: r.i });
          if (r.u) items.push({ type: 'rect', x: x0 + r.x, y: baseline + fs * 0.1, w: r.width - (/\s$/.test(r.t) ? 0 : 0), h: Math.max(0.9, fs * 0.07), fill: r.c });
        });
        if (k === 0 && list) {
          if (list.type === 'disc') {
            items.push({ type: 'circle', cx: textX - E.LIST.discCenterFromText * (fs / 13.3334), cy: baseline - fs * E.LIST.discLift, r: E.LIST.discR * (fs / 13.3334), fill: runs[0].c });
          } else {
            var mk = list.type === 'decimal' ? list.n + '.' : list.type === 'alpha' ? String.fromCharCode(96 + list.n) + '.' : romanize(list.n) + '.';
            var mw = list.markerWeight || runs[0].w || 300;
            var mm = measure(mk, fkey(mw, false), fs, lsPx);
            items.push({ type: 'text', x: textX - E.LIST.markerGap * (fs / 13.3334) - mm.width, y: baseline, t: mk, fk: fkey(mw, false), size: fs, color: runs[0].c, ls: lsPx, segs: mm.segs, width: mm.width });
          }
        }
        lineInfo.push({ paraIndex: pi, line: k, baseline: baseline, top: spec.top + li * adv, width: lw });
        li++;
      });
    });
    // height: last non-blank line counts like Canva (blank trailing lines included when present)
    var n = li;
    return { items: items, lines: lineInfo, nLines: n, adv: adv, height: n ? h1 + (n - 1) * adv : 0, h1: h1 };
  }
  E.block = block;

  function trailingSpaceW(placed, fs, ls) {
    var last = placed[placed.length - 1]; if (!last) return 0;
    var m = /\s+$/.exec(last.t); if (!m) return 0;
    return measure(m[0], fkey(last.w, last.i), last.size, last.ls).width;
  }

  // ---------- helpers ----------
  var BULAN = ['Januari', 'Februari', 'Maret', 'April', 'Mei', 'Juni', 'Juli', 'Agustus', 'September', 'Oktober', 'November', 'Desember'];
  function parseDate(iso) { var p = String(iso || '').split('-'); return { y: +p[0], m: +p[1], d: +p[2] }; }
  function pad(n) { return (n < 10 ? '0' : '') + n; }
  var MONTH_EN = ['January', 'February', 'March', 'April', 'May', 'June', 'July', 'August', 'September', 'October', 'November', 'December'];
  E.dateLong = function (iso, lang) { var d = parseDate(iso); return pad(d.d) + ' ' + (lang === 'en' ? MONTH_EN : BULAN)[d.m - 1] + ' ' + d.y; };
  E.dateShort = function (iso) { var d = parseDate(iso); return pad(d.d) + ' - ' + pad(d.m) + ' - ' + d.y; };

  function grp(n) { return String(n).replace(/\B(?=(\d{3})+(?!\d))/g, '.'); }
  E.rupiah = function (n) {
    var neg = n < 0; n = Math.abs(n);
    var whole = Math.floor(n + 1e-9), frac = Math.round((n - whole) * 100);
    return (neg ? '-' : '') + 'Rp ' + grp(whole) + (frac ? ',' + pad(frac) : ',-');
  };
  E.num = function (n) {
    var whole = Math.floor(n + 1e-9), frac = Math.round((n - whole) * 100);
    if (!frac) return grp(whole);
    var f = String(frac).padStart(2, '0').replace(/0$/, '');
    return grp(whole) + ',' + f;
  };

  var SAT = ['', 'Satu', 'Dua', 'Tiga', 'Empat', 'Lima', 'Enam', 'Tujuh', 'Delapan', 'Sembilan', 'Sepuluh', 'Sebelas'];
  function tb(n) {
    n = Math.floor(n);
    if (n < 12) return SAT[n];
    if (n < 20) return tb(n - 10) + ' Belas';
    if (n < 100) return tb(Math.floor(n / 10)) + ' Puluh' + (n % 10 ? ' ' + tb(n % 10) : '');
    if (n < 200) return 'Seratus' + (n - 100 ? ' ' + tb(n - 100) : '');
    if (n < 1000) return tb(Math.floor(n / 100)) + ' Ratus' + (n % 100 ? ' ' + tb(n % 100) : '');
    if (n < 2000) return 'Seribu' + (n - 1000 ? ' ' + tb(n - 1000) : '');
    if (n < 1e6) return tb(Math.floor(n / 1000)) + ' Ribu' + (n % 1000 ? ' ' + tb(n % 1000) : '');
    if (n < 1e9) return tb(Math.floor(n / 1e6)) + ' Juta' + (n % 1e6 ? ' ' + tb(n % 1e6) : '');
    if (n < 1e12) return tb(Math.floor(n / 1e9)) + ' Miliar' + (n % 1e9 ? ' ' + tb(n % 1e9) : '');
    return tb(Math.floor(n / 1e12)) + ' Triliun' + (n % 1e12 ? ' ' + tb(n % 1e12) : '');
  }
  var ONES = ['', 'One', 'Two', 'Three', 'Four', 'Five', 'Six', 'Seven', 'Eight', 'Nine', 'Ten', 'Eleven', 'Twelve', 'Thirteen', 'Fourteen', 'Fifteen', 'Sixteen', 'Seventeen', 'Eighteen', 'Nineteen'];
  var TENS = ['', '', 'Twenty', 'Thirty', 'Forty', 'Fifty', 'Sixty', 'Seventy', 'Eighty', 'Ninety'];
  function en(n) {
    n = Math.floor(n);
    if (n < 20) return ONES[n];
    if (n < 100) return TENS[Math.floor(n / 10)] + (n % 10 ? ' ' + ONES[n % 10] : '');
    if (n < 1000) return ONES[Math.floor(n / 100)] + ' Hundred' + (n % 100 ? ' ' + en(n % 100) : '');
    var units = [[1e12, 'Trillion'], [1e9, 'Billion'], [1e6, 'Million'], [1e3, 'Thousand']];
    for (var i = 0; i < units.length; i++) if (n >= units[i][0]) { var q = Math.floor(n / units[i][0]), r = n % units[i][0]; return en(q) + ' ' + units[i][1] + (r ? ' ' + en(r) : ''); }
    return '';
  }
  E.terbilang = function (n, lang) {
    n = Math.round(n);
    if (lang === 'en') return n === 0 ? 'Zero Rupiah' : en(n).replace(/\s+/g, ' ').trim() + ' Rupiah';
    return n === 0 ? 'Nol Rupiah' : tb(n).replace(/\s+/g, ' ').trim() + ' Rupiah';
  };

  // ---------- money ----------
  E.compute = function (d) {
    var p = d.pricing || {};
    var area = +d.area || 0;
    var base = p.mode === 'unit' ? (+p.unitPrice || 0) : area * (+p.pricePerM2 || 0);
    var cb = 0;
    if (p.cashbackOn) {
      cb = p.cashbackType === 'nominal' ? (+p.cashbackValue || 0) : base * (+p.cashbackValue || 0) / 100;
    }
    var fin = base - cb;
    var terms = (d.terms || []).map(function (t) { return Math.round(fin * (+t.pct || 0) / 100 * 100) / 100; });
    var pctSum = (d.terms || []).reduce(function (a, t) { return a + (+t.pct || 0); }, 0);
    return { base: base, cashback: cb, final: fin, terms: terms, pctSum: pctSum };
  };

  // ---------- shared page pieces ----------
  function footer(items, opts) {
    items.push({ type: 'rect', x: 0, y: 1036.0867, w: W, h: H - 1036.0867, fill: GREEN });
    if (!opts || opts.icon !== false) items.push({ type: 'image', key: 'icon', x: 54.2473, y: 1064.3920, w: 32.5477, h: 28.6827 });
    var em = block({ x: opts && opts.icon === false ? 54.2473 : 94.3173, top: 1074.1517, width: 330, fs: 11.7446, lh: 1.1, color: CREAM, paras: [{ runs: [R(opts && opts.email || 'info.wijayamegahwisesa@gmail.com', 400)] }] });
    push(items, em.items);
    logo(items, 658.4578, 1068.2724, 21.1130, CREAM);
  }

  // logo group (s ■▲● ma). geometry from Canva group, scaled from footer version (fs 21.113 at x0,y0)
  function logo(items, x0, y0, fs, color) {
    var s = fs / 21.11302105400462;
    function X(v) { return x0 + (v - 658.4578) * s; }
    function Y(v) { return y0 + (v - 1068.2724) * s; }
    push(items, block({ x: X(658.4578), top: Y(1068.2724), width: 40 * s, fs: fs, lh: 1.1, color: color, paras: [{ runs: [R('s', 700)] }] }).items);
    push(items, block({ x: X(707.8858), top: Y(1068.2724), width: 60 * s, fs: fs, lh: 1.1, color: color, paras: [{ runs: [R('ma', 700)] }] }).items);
    // heads
    items.push({ type: 'rect', x: X(673.9719), y: Y(1076.8621), w: 5.7394 * s, h: 5.7394 * s, fill: color });
    items.push({ type: 'tri', x: X(686.1084), y: Y(1076.8621), w: 6.5009 * s, h: 5.6883 * s, fill: color });
    // avatar figure (round head + shoulders)
    avatar(items, X(696.6070), Y(1076.8621), 10.5381 * s, 11.8527 * s, color, false);
    // bodies under square & triangle
    avatar(items, X(671.5725), Y(1082.9692) - 6.1071 * s, 10.5381 * s, 11.8527 * s, color, true);
    avatar(items, X(684.0897), Y(1082.9692) - 6.1071 * s, 10.5381 * s, 11.8527 * s, color, true);
  }
  // avatar icon box (w x h). bodyOnly draws only the bottom part (rows >= 0.5153h)
  function avatar(items, x, y, w, h, color, bodyOnly) {
    var A = E.AVATAR;
    var bodyTop = y + h * A.bodyTop;
    items.push({ type: 'dome', x: x + w * A.bodyInset, y: bodyTop, w: w * (1 - 2 * A.bodyInset), h: y + h - bodyTop, fill: color, clipTop: bodyOnly ? y + h * 0.51526 : null });
    if (!bodyOnly) items.push({ type: 'circle', cx: x + w * 0.5, cy: y + h * A.headCy, r: w * A.headR, fill: color });
  }
  E.AVATAR = { bodyTop: 0.535, bodyInset: 0.0, headCy: 0.235, headR: 0.215, k: 0.78 };

  function push(a, b) { for (var i = 0; i < b.length; i++) a.push(b[i]); }
  function P(runs, extra) { return Object.assign({ runs: runs }, extra || {}); }
  var BLANK = { blank: true };

  // ---------- strings ----------
  var STR = {
    id: {
      header1: 'PROPOSAL PENAWARAN ', header2: 'JASA DESAIN ARSITEKTUR',
      to: 'Kepada Yth:',
      greet: function () { return 'Dengan hormat,'; },
      letter: function (svc, proj) { return [R('Terima kasih atas kesempatan dan kepercayaan yang diberikan kepada kami untuk mengajukan proposal jasa desain ' + svc + ' untuk proyek ' + proj + '. Proposal ini berisi ruang lingkup pekerjaan, ', 300), R('output/deliverables', 300, { i: true }), R(', biaya jasa, dan ', 300), R('term of payment', 300, { i: true }), R('.', 300)]; },
      s1: '1.  Informasi Proyek', lProject: ' Proyek ', lLocation: ' Lokasi ', lArea: 'Luas Area',
      s2: '2.  Ruang Lingkup Pekerjaan',
      s3: '3.  Investasi Desain ( Fee Proposal )',
      areaCalc: 'Luas Area Design Terhitung : ', perM2: 'Harga Desain per m² : ',
      totalFee: 'TOTAL FEE DESAIN ARSITEKTUR ( ', afterCb: 'Fee After Cashback',
      bonusIntro: 'Nilai tersebut sudah termasuk beberapa fasilitas tambahan seperti :',
      s4a: '4.  ', s4b: 'Term Of Payment', tableHead: 'Tahap Pembayaran Persentase Nominal',
      terms: 'Ketentuan:', termsNote: 'Invoice jatuh tempo maksimal 7 hari kalender setelah dikirimkan. Bila terdapat keterlambatan pembayaran > 14 hari, pekerjaan dihentikan sementara hingga pembayaran diterima.',
      s5: '5.   Perhitungan Estimasi Awal RAB',
      rab: [[R('Perhitungan Estimasi Awal RAB (RAB kasar) akan dilakukan setelah diterimanya pembayaran DP.', 300)],
        [R('Apabila setelah client mendapatkan Estimasi Awal RAB, project ini tetap berlanjut, maka proses pekerjaan otomatis diteruskan.', 300)],
        [R('Namun apabila setelah client mendapatkan Estimasi Awal RAB, project ini tidak berlanjut, maka DP akan dikembalikan dan client akan memberikan ', 300), R('compensation fee', 300, { i: true }), R('.', 300)]],
      s6: '6.  Durasi Pekerjaan',
      totalEst: function (v) { return [R('> Total estimasi: ', 400), R(v, 700), R(', tergantung kecepatan ', 400), R('feedback', 400, { i: true }), R(' dari client.', 400)]; },
      s7: '7.   Hak Cipta / Ownership',
      own: ['Desain adalah milik konsultan hingga seluruh pembayaran selesai.', 'Client mendapatkan hak penuh untuk penggunaan desain setelah seluruh fee dilunasi.', 'Dilarang menggunakan desain untuk proyek lain tanpa persetujuan tertulis.'],
      s8: '8. Validity', valid: function (n) { return 'Proposal ini berlaku ' + n + ' hari kalender sejak tanggal pengajuan.'; },
      concl: 'Conclusion',
      conclText: function (co, who) { return [R('Kami berharap proposal ini dapat menjadi dasar kerjasama yang baik antara ' + co + ' dengan ' + who + ' Apabila proposal ini sesuai, mohon menandatangani halaman ini beserta pembayaran ', 400), R('Down Payment', 400, { i: true }), R(' sebagai bentuk persetujuan untuk dimulainya pekerjaan.', 400)]; },
      approved: 'Disetujui Oleh : ', date: 'Date : '
    },
    en: {
      header1: 'PROPOSAL FOR ', header2: 'ARCHITECTURAL DESIGN SERVICES',
      to: 'To:',
      greet: function (who) { return who ? 'Dear ' + who + ',' : 'Dear Sir/Madam,'; },
      letter: function (svc, proj) { return [R('Thank you for the opportunity and trust given to us to submit a proposal for ' + svc + ' design services for the ' + proj + ' project. This proposal covers the scope of work, ', 300), R('output/deliverables', 300, { i: true }), R(', service fees, and ', 300), R('terms of payment', 300, { i: true }), R('.', 300)]; },
      s1: '1.  Project Information', lProject: ' Project ', lLocation: ' Location ', lArea: 'Area',
      s2: '2.  Scope of Work',
      s3: '3.  Design Investment ( Fee Proposal )',
      areaCalc: 'Calculated Design Area : ', perM2: 'Design Fee per m² : ',
      totalFee: 'TOTAL ARCHITECTURAL DESIGN FEE ( ', afterCb: 'Fee After Cashback',
      bonusIntro: 'This fee already includes the following additional facilities :',
      s4a: '4.  ', s4b: 'Terms Of Payment', tableHead: 'Payment Stage Percentage Amount',
      terms: 'Terms:', termsNote: 'Invoices are due no later than 7 calendar days after issuance. If payment is delayed by more than 14 days, work will be suspended until payment is received.',
      s5: '5.   Preliminary Cost Estimate (RAB)',
      rab: [[R('The preliminary cost estimate (rough RAB) will be prepared after the down payment is received.', 300)],
        [R('If the project continues after the client receives the preliminary cost estimate, the work will proceed automatically.', 300)],
        [R('However, if the project does not continue after the client receives the preliminary cost estimate, the down payment will be refunded and the client will pay a ', 300), R('compensation fee', 300, { i: true }), R('.', 300)]],
      s6: '6.  Project Duration',
      totalEst: function (v) { return [R('> Total estimate: ', 400), R(v, 700), R(', depending on the speed of ', 400), R('feedback', 400, { i: true }), R(' from the client.', 400)]; },
      s7: '7.   Copyright / Ownership',
      own: ['The design remains the property of the consultant until full payment is completed.', 'The client obtains full rights to use the design once all fees have been paid.', 'The design may not be used for other projects without written approval.'],
      s8: '8. Validity', valid: function (n) { return 'This proposal is valid for ' + n + ' calendar days from the date of submission.'; },
      concl: 'Conclusion',
      conclText: function (co, who) { return [R('We hope this proposal can serve as the basis for a good collaboration between ' + co + ' and ' + who + '. If this proposal is acceptable, please sign this page and make the ', 400), R('Down Payment', 400, { i: true }), R(' as a sign of approval to commence the work.', 400)]; },
      approved: 'Approved By : ', date: 'Date : '
    }
  };
  E.STR = STR;
  var SVC_EN = { 'arsitektur-interior': 'architecture-interior', 'arsitektur': 'architecture', 'interior': 'interior', 'arsitektur dan interior': 'architecture and interior' };

  // ---------- pages ----------
  var LIMIT = 1012, TOP = 52.7087, TOPC = 79.3701, FS = 13.3334;

  E.layout = function (d) {
    var money = E.compute(d);
    var S = STR[d.lang === 'en' ? 'en' : 'id'];
    var pages = [cover(d)];
    var cur = null;
    function newPage(top, spill) { cur = { items: [], top: top, y: null, spill: !!spill }; pages.push(cur); return cur; }
    function place(sec) {
      var top = cur.y == null ? cur.top : cur.y + sec.gap;
      var r = sec.build(top);
      if (top + r.height > LIMIT && cur.y != null) {
        newPage(TOP, true);
        top = cur.top; r = sec.build(top);
      }
      if (top + r.height > LIMIT) cur.overflow = true;
      push(cur.items, r.items);
      cur.y = top + r.height;
    }
    function startGroup(top) { if (!cur || !cur.spill) newPage(top, false); }

    // group A: letter page
    var head = page2Head(d, S);
    cur = { items: head.items, top: head.next, y: null, spill: false }; pages.push(cur);
    place({ gap: 0, build: function (t) { return sec1(d, S, t); } });
    place({ gap: 40.0, build: function (t) { return sec2(d, S, t); } });
    // group B: investment, terms, RAB, duration
    startGroup(TOP);
    place({ gap: 26.0, build: function (t) { return sec3(d, S, money, t); } });
    place({ gap: 25.5, build: function (t) { return sec4(d, S, money, t); } });
    place({ gap: 10.0, build: function (t) { return sec5(S, t); } });
    place({ gap: 25.9937, build: function (t) { return sec6(d, S, t); } });
    // group C: ownership, validity, conclusion, signature
    startGroup(TOPC);
    place({ gap: 26.0, build: function (t) { return sec7(S, t); } });
    place({ gap: 26.9969, build: function (t) { return sec8(d, S, t); } });
    place({ gap: 30.9934, build: function (t) { return sec9(d, S, t); } });
    var sigTop = Math.max(647.3545, cur.y + 30);
    if (sigTop + 190 > LIMIT) { newPage(TOPC, false); sigTop = 647.3545; }
    push(cur.items, signature(d, S, sigTop));
    pages.forEach(function (p, i) { if (i) footer(p.items); });
    return { pages: pages, money: money };
  };

  function who(d) { return ((d.clientTitle ? d.clientTitle + ' ' : '') + (d.clientName || '')).trim(); }
  function projName(d) { return d.projectTitleCase || titleCase(d.projectName); }

  function page2Head(d, S) {
    var it = [], L = 54.2473, Wd = 685.2062, city = d.city || 'Bogor';
    push(it, block({ x: L, top: 54.2473, width: Wd, fs: 23.9999, lh: 1.4, ls: 0.05, paras: [P([R(S.header1, 700)]), P([R(S.header2, 700)])] }).items);
    var t = block({ x: L, top: 195.1677, width: Wd, fs: 23.9999, lh: 1.4, ls: 0.05, paras: [P([R(String(d.projectName || '').replace(/\n/g, ' ').toUpperCase(), 700)])] });
    push(it, t.items);
    var dy = (t.nLines - 1) * t.adv;
    push(it, block({ x: L, top: 223.3677 + dy, width: Wd, fs: 12.0002, lh: 1.4, ls: 0.05, paras: [P([R(city + ', ' + E.dateShort(d.date), 300)])] }).items);
    var kp = [P([R(S.to, 300)]), P([R(who(d), 300)]), P([R(projName(d), 300)])];
    var k = block({ x: L, top: 312.8556 + dy, width: Wd, fs: 12.0002, lh: 1.4, ls: 0.05, paras: kp });
    push(it, k.items);
    dy += Math.max(0, k.nLines - 3) * 16;
    var svc = d.serviceType || 'arsitektur-interior';
    if (d.lang === 'en') svc = SVC_EN[svc.toLowerCase()] || svc;
    var letter = block({ x: L, top: 402.4379 + dy, width: Wd, fs: 12.0002, lh: 1.4, ls: 0.05, paras: [P([R(S.greet(who(d)), 300)]), P(S.letter(svc, projName(d)))] });
    push(it, letter.items);
    dy += (letter.nLines - 4) * 16;
    return { items: it, next: 485.0203 + dy };
  }

  function sec1(d, S, I) {
    var it = [], L = 54.2473, fs = FS;
    push(it, block({ x: L, top: I, width: 342.6, fs: fs, lh: 1.78, paras: [P([R(S.s1, 700)])] }).items);
    var vals = [[R(': ' + projName(d), 300)], [R(': ' + (d.location || ''), 300)], [R(': ', 300), R('± ' + E.num(+d.area || 0) + ' m2 ', 700)]];
    var vy = I + 23;
    vals.forEach(function (v, idx) {
      var vb = block({ x: 303.3604, top: vy, width: 436.0931, fs: fs, lh: 1.78, paras: [P(v)] });
      push(it, vb.items);
      if (idx === 2) push(it, block({ x: L, top: vy, width: 342.6, fs: fs, lh: 1.78, paras: [P([R('         ', 300), R('c', 500), R('. ' + S.lArea + ' ', 300)])] }).items);
      else push(it, block({ x: L, top: vy, width: 342.6, fs: fs, lh: 1.78, paras: [P([R(idx ? S.lLocation : S.lProject, 300)], { list: { type: 'alpha', level: 2, n: idx + 1 } })] }).items);
      vy += vb.nLines * 23;
    });
    return { items: it, height: 15.2666 + ((vy - I) / 23 - 1) * 23 };
  }

  function sec2(d, S, top) {
    var sp = [P([R(S.s2, 700)])];
    (d.scope || []).forEach(function (ph, pi) {
      sp.push(P([R(' ' + ph.title, 300)], { list: { type: 'alpha', level: 2, n: pi + 1 } }));
      (ph.items || []).forEach(function (s, si) { sp.push(P([R(' ', 300)].concat(md(s, 300)), { list: { type: 'roman', level: 3, n: si + 1 } })); });
    });
    var sb = block({ x: 54.2473, top: top, width: 685.2062, fs: FS, lh: 1.78, paras: sp });
    return { items: sb.items, height: sb.height };
  }

  function titleCase(s) {
    return String(s || '').replace(/\n/g, ' ').toLowerCase().replace(/(^|\s|\()([a-z])/g, function (m, a, b) { return a + b.toUpperCase(); });
  }
  E.titleCase = titleCase;

  function sec3(d, S, money, top) {
    var it = [], L = 54.2473, B = 76.4702, fs = FS, p = d.pricing || {}, lang = d.lang;
    push(it, block({ x: L, top: top, width: 685.2, fs: fs, lh: 1.78, paras: [P([R(S.s3, 700)])] }).items);
    var areaTxt = E.num(+d.area || 0) + ' m2', inv = [];
    if (p.mode !== 'unit') {
      inv.push(P([R(S.areaCalc + areaTxt, 300)]));
      inv.push(P([R(S.perM2, 300), R('Rp. ' + E.num(+p.pricePerM2 || 0) + ' / m²', 700)]));
      inv.push(BLANK);
    }
    inv.push(P([R(S.totalFee + areaTxt + ')', 700)]));
    inv.push(P([R(E.rupiah(money.base) + ' ( ' + E.terbilang(money.base, lang) + ' )', 700)]));
    if (p.cashbackOn) {
      inv.push(BLANK);
      var cbr = [R('>', 700, { c: BLACK }), R('CASHBACK', 700, { c: BLACK, u: true })];
      if (p.cashbackShowPct) cbr.push(R(' ' + (p.cashbackType === 'nominal' ? E.rupiah(money.cashback) : E.num(+p.cashbackValue || 0) + '%'), 700, { c: BLACK }));
      inv.push(P(cbr));
      inv.push(P([R(S.afterCb, 700, { c: BLACK })]));
      inv.push(P([R(E.rupiah(money.final) + ' ( ' + E.terbilang(money.final, lang) + ' )', 700, { c: GREEN })]));
    }
    if (p.bonusOn && (p.bonusItems || []).filter(Boolean).length) {
      inv.push(BLANK);
      inv.push(P([R(S.bonusIntro, 400)]));
      p.bonusItems.filter(Boolean).forEach(function (b) { inv.push(P(md(b, 700), { list: { type: 'disc', level: 1 } })); });
    }
    var ib = block({ x: B, top: top + 25.1227, width: 685.2062, fs: fs, lh: 1.78, paras: inv });
    push(it, ib.items);
    return { items: it, height: 25.1227 + ib.height };
  }

  function sec4(d, S, money, T4) {
    var it = [], L = 54.2473, B = 76.4702, fs = FS;
    push(it, block({ x: L, top: T4, width: 685.2, fs: fs, lh: 1.78, paras: [P([R(S.s4a, 700), R(S.s4b, 700, { i: true })])] }).items);
    var TT = T4 + 34.2667;
    var tp = [P([R(S.tableHead, 300)]), BLANK];
    (d.terms || []).forEach(function (t, i) { tp.push(P([R(' ' + t.label + ' ', 300), R(E.num(+t.pct || 0) + '% ', 700)], { list: { type: 'decimal', level: 1, n: i + 1 } })); });
    var tbk = block({ x: B, top: TT, width: 427.0174, fs: fs, lh: 1.78, paras: tp });
    var itemLines = tbk.nLines - 2;
    tbk.lines.forEach(function (ln) {
      if (ln.paraIndex >= 2 && ln.line === 0) push(it, block({ x: 615.6920, top: ln.top - 1.9667, width: 160, fs: fs, lh: 1.78, paras: [P([R(E.rupiah(money.terms[ln.paraIndex - 2] || 0), 700)])] }).items);
    });
    push(it, tbk.items);
    var totTop = TT + (2 + itemLines + 1) * 23 - 3.7069;
    push(it, block({ x: B, top: totTop, width: 674.28, fs: fs, lh: 1.78, paras: [P([R('T', 300), R('OTAL', 400), R(' ' + E.num(money.pctSum) + '%', 700)])] }).items);
    push(it, block({ x: E.TOTAL_X, top: totTop, width: 170, fs: fs, lh: 1.78, paras: [P([R(E.rupiah(money.final), 700)])] }).items);
    var kt = block({ x: B, top: TT + (2 + itemLines + 3) * 23, width: 427.0174, fs: fs, lh: 1.78, paras: [P([R(S.terms, 400)]), P([R(S.termsNote, 400)], { list: { type: 'disc', level: 1 } })] });
    push(it, kt.items);
    var termH = 15.2666 + (2 + itemLines + 3 + kt.nLines) * 23;
    return { items: it, height: 34.2667 + termH };
  }

  function sec5(S, T5) {
    var it = [];
    push(it, block({ x: 54.2473, top: T5, width: 685.2, fs: FS, lh: 1.78, paras: [P([R(S.s5, 700)])] }).items);
    var rb = block({ x: 76.4702, top: T5 + 25.1228, width: 654.2989, fs: FS, lh: 1.78, paras: S.rab.map(function (r) { return P(r, { list: { type: 'disc', level: 1 } }); }) });
    push(it, rb.items);
    return { items: it, height: 25.1228 + rb.height };
  }

  function sec6(d, S, T6) {
    var it = [];
    push(it, block({ x: 54.2473, top: T6, width: 685.2, fs: FS, lh: 1.78, paras: [P([R(S.s6, 700)])] }).items);
    var dp = (d.duration || []).map(function (r) { return P([R(r.label + ' ', 300), R(r.value || '', 700)], { list: { type: 'disc', level: 1 } }); });
    dp.push(P(S.totalEst(d.durationTotal || '')));
    var db = block({ x: 76.4702, top: T6 + 34.2667, width: 662.9833, fs: FS, lh: 1.78, paras: dp });
    push(it, db.items);
    return { items: it, height: 34.2667 + db.height };
  }
  E.TOTAL_X = 615.6920;

  function sec7(S, top) {
    var it = [];
    push(it, block({ x: 60.3031, top: top, width: 685.2, fs: FS, lh: 1.78, paras: [P([R(S.s7, 700)])] }).items);
    var b = block({ x: 82.5259, top: top + 25.1228, width: 685.2062, fs: FS, lh: 1.78, paras: S.own.map(function (s) { return P([R(s, 300)], { list: { type: 'disc', level: 1 } }); }) });
    push(it, b.items);
    return { items: it, height: 25.1228 + b.height };
  }
  function sec8(d, S, top) {
    var it = [];
    push(it, block({ x: 60.3031, top: top, width: 685.2, fs: FS, lh: 1.78, paras: [P([R(S.s8, 700)])] }).items);
    var b = block({ x: 82.5259, top: top + 34.2666, width: 662.9833, fs: FS, lh: 1.78, paras: [P([R(S.valid(d.validityDays || 14), 300)])] });
    push(it, b.items);
    return { items: it, height: 34.2666 + b.height };
  }
  function sec9(d, S, top) {
    var it = [];
    push(it, block({ x: 60.3031, top: top, width: 685.2, fs: FS, lh: 1.78, paras: [P([R(S.concl, 700)])] }).items);
    var b = block({ x: 60.3031, top: top + 34.2667, width: 677.4652, fs: FS, lh: 1.78, paras: [P(S.conclText(d.signCompany || 'WMW Construction', who(d)))] });
    push(it, b.items);
    return { items: it, height: 34.2667 + b.height };
  }
  function signature(d, S, top) {
    var it = [], o = top - 647.3545, company = d.signCompany || 'WMW Construction';
    it.push({ type: 'image', key: 'signature', x: 106.9351, y: 654.9879 + o, w: 92.6667, h: 142.6667 });
    push(it, block({ x: 54.2473, top: 647.3545 + o, width: 208.1881, fs: FS, lh: 1.78, align: 'center', paras: [P([R(company, 400)])] }).items);
    push(it, block({ x: 531.2654, top: 647.3545 + o, width: 208.1881, fs: FS, lh: 1.78, align: 'center', paras: [P([R(S.approved, 400)])] }).items);
    push(it, block({ x: 54.2473, top: 797.6212 + o, width: 208.1881, fs: FS, lh: 1.78, align: 'center', paras: [P([R(d.signer || 'Jamie Wijaya Halim', 400)])] }).items);
    push(it, block({ x: 554.9382, top: 796.6212 + o, width: 170, fs: FS, lh: 1.78, paras: [P([R('(...............................................)', 400)]), P([R(S.date, 400)])] }).items);
    return it;
  }

  function cover(d) {
    var it = [];
    var city = d.city || 'Bogor', dl = city + ', ' + E.dateLong(d.date, d.lang);
    if (d.coverPhoto && E.images.coverPhoto) {
      it.push({ type: 'image', key: 'coverPhoto', x: 0, y: 0, w: W, h: 1043.1496, fit: 'cover', opacity: 0.46 });
      logo(it, 54.2473, 79.3701, 47.1327, GREEN);
      push(it, block({ x: 57.2696, top: 126.8218, width: 58.2567, fs: 9.3979, lh: 1.1, ls: 0.2, color: GREEN, paras: [P([R('studio', 400)])] }).items);
      push(it, block({ x: 174.7020, top: 126.8844, width: 58.2567, fs: 9.3196, lh: 1.1, ls: 0.2, align: 'end', color: GREEN, paras: [P([R('saaama', 400)])] }).items);
      push(it, block({ x: 583.2757, top: 101.4488, width: 158.9797, fs: 14.5183, lh: 1.1, align: 'end', color: GREEN, paras: [P([R('architecture design', 400)]), P([R('service proposal', 400)])] }).items);
      var paras = String(d.projectName || '').toUpperCase().split('\n').map(function (l) { return P([R(l, 700)]); });
      if (d.coverSubtitle) String(d.coverSubtitle).toUpperCase().split('\n').forEach(function (l) { paras.push(P([R(l, 400)])); });
      var tb = block({ x: 54.2473, top: 227.3785, width: 660.0834, fs: 48.4066, lh: 1.1, color: GREEN, paras: paras });
      push(it, tb.items);
      push(it, block({ x: 57.0493, top: 227.3785 + tb.height, width: 685.2, fs: 12.0002, lh: 1.4, ls: 0.05, color: GREEN, paras: [P([R(dl, 300)])] }).items);
      footer(it);
      return { items: it };
    }
    push(it, block({ x: 54.2473, top: 79.3701, width: 262.9, fs: 24.0087, lh: 1.1, color: GREEN, paras: [P([R('architecture design', 400)]), P([R('service proposal', 400)])] }).items);
    var tparas = String(d.projectName || '').toUpperCase().split('\n').map(function (l) { return P([R(l, 700)]); });
    var t = block({ x: 54.2473, top: 284.3240, width: 644.7083, fs: 57.7142, lh: 1.1, color: GREEN, paras: tparas });
    push(it, t.items);
    var dTop = t.nLines > 1 ? 284.3240 + 68.0374 + (t.nLines - 1) * t.adv : 284.3240 + 61.2513;
    push(it, block({ x: 57.0493, top: dTop, width: 685.2, fs: 12.0002, lh: 1.4, ls: 0.05, color: GREEN, paras: [P([R(dl, 300)])] }).items);
    footer(it);
    return { items: it };
  }

  // ---------- HTML renderer ----------
  var FAM = "'SaaamaSans', 'Open Sauce Sans', sans-serif";
  function esc(s) { return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;'); }
  E.renderHTML = function (page) {
    var h = '';
    page.items.forEach(function (o) {
      if (o.type === 'text') {
        var w = o.fk[0] === 'L' ? 300 : o.fk[0] === 'M' ? 500 : o.fk[0] === 'B' ? 700 : 400;
        h += '<span style="position:absolute;white-space:pre;left:' + o.x.toFixed(3) + 'px;top:' + (o.y - o.size).toFixed(3) + 'px;font:' + (o.fk.indexOf('I') > 0 ? 'italic ' : '') + w + ' ' + o.size.toFixed(4) + 'px/' + (o.size * 1.237).toFixed(4) + 'px ' + FAM + ';letter-spacing:' + (o.ls || 0).toFixed(4) + 'px;color:' + o.color + '">' + esc(o.t) + '</span>';
      } else if (o.type === 'rect') {
        h += '<div style="position:absolute;left:' + o.x + 'px;top:' + o.y + 'px;width:' + o.w + 'px;height:' + o.h + 'px;background:' + o.fill + '"></div>';
      } else if (o.type === 'circle') {
        h += '<div style="position:absolute;left:' + (o.cx - o.r) + 'px;top:' + (o.cy - o.r) + 'px;width:' + 2 * o.r + 'px;height:' + 2 * o.r + 'px;border-radius:50%;background:' + o.fill + '"></div>';
      } else if (o.type === 'tri') {
        h += '<svg style="position:absolute;left:' + o.x + 'px;top:' + o.y + 'px;overflow:visible" width="' + o.w + '" height="' + o.h + '"><path d="M' + o.w / 2 + ' 0L' + o.w + ' ' + o.h + 'H0Z" fill="' + o.fill + '"/></svg>';
      } else if (o.type === 'dome') {
        var top = o.clipTop != null ? o.clipTop : o.y;
        var ry = o.h, rx = o.w / 2;
        h += '<svg style="position:absolute;left:' + o.x + 'px;top:' + top + 'px;overflow:hidden" width="' + o.w + '" height="' + (o.y + o.h - top) + '"><path d="' + domePath(0, o.y - top, o.w, o.h) + '" fill="' + o.fill + '"/></svg>';
      } else if (o.type === 'image') {
        var src = E.images[o.key]; if (!src) return;
        if (o.fit === 'cover') {
          h += '<div style="position:absolute;left:' + o.x + 'px;top:' + o.y + 'px;width:' + o.w + 'px;height:' + o.h + 'px;background:url(' + src + ') center/cover no-repeat;opacity:' + (o.opacity || 1) + '"></div>';
        } else {
          h += '<img alt="" src="' + src + '" style="position:absolute;left:' + o.x + 'px;top:' + o.y + 'px;width:' + o.w + 'px;height:' + o.h + 'px;max-width:none">';
        }
      }
    });
    return h;
  };
  // half-ellipse dome: flat bottom at y+h
  function domePath(x, y, w, h) {
    var k = E.AVATAR.k, rx = w / 2, cx = x + rx, by = y + h;
    return 'M' + x + ' ' + by + 'C' + x + ' ' + (by - h * k) + ' ' + (cx - rx * k) + ' ' + y + ' ' + cx + ' ' + y + 'C' + (cx + rx * k) + ' ' + y + ' ' + (x + w) + ' ' + (by - h * k) + ' ' + (x + w) + ' ' + by + 'Z';
  }

  // ---------- PDF renderer ----------
  E.toPDF = function (pages, coverImgData) {
    var jsPDF = global.jspdf.jsPDF;
    var doc = new jsPDF({ unit: 'pt', format: [595.2756, 841.8898], compress: true });
    Object.keys(E.fontB64).forEach(function (k) {
      doc.addFileToVFS(k + '.ttf', E.fontB64[k]);
      doc.addFont(k + '.ttf', 'OS', k);
    });
    var S = 0.75;
    function col(hex) { return [parseInt(hex.substr(1, 2), 16), parseInt(hex.substr(3, 2), 16), parseInt(hex.substr(5, 2), 16)]; }
    pages.forEach(function (pg, pi) {
      if (pi) doc.addPage([595.2756, 841.8898]);
      pg.items.forEach(function (o) {
        if (o.type === 'text') {
          doc.setFont('OS', o.fk); doc.setFontSize(o.size * S);
          var c = col(o.color); doc.setTextColor(c[0], c[1], c[2]);
          o.segs.forEach(function (sg) {
            if (!sg.t) return;
            doc.text(sg.t, (o.x + sg.dx) * S, o.y * S, { baseline: 'alphabetic', charSpace: (o.ls || 0) * S });
          });
        } else if (o.type === 'rect') {
          var c2 = col(o.fill); doc.setFillColor(c2[0], c2[1], c2[2]);
          doc.rect(o.x * S, o.y * S, o.w * S, o.h * S, 'F');
        } else if (o.type === 'circle') {
          var c3 = col(o.fill); doc.setFillColor(c3[0], c3[1], c3[2]);
          doc.circle(o.cx * S, o.cy * S, o.r * S, 'F');
        } else if (o.type === 'tri') {
          var c4 = col(o.fill); doc.setFillColor(c4[0], c4[1], c4[2]);
          doc.triangle((o.x + o.w / 2) * S, o.y * S, (o.x + o.w) * S, (o.y + o.h) * S, o.x * S, (o.y + o.h) * S, 'F');
        } else if (o.type === 'dome') {
          var c5 = col(o.fill); doc.setFillColor(c5[0], c5[1], c5[2]);
          var top = o.clipTop != null ? o.clipTop : o.y;
          // clip by drawing only the part below 'top' : approximate with full dome when clipTop<=y
          var x = o.x, y = o.y, w = o.w, h = o.h, k = E.AVATAR.k, rx = w / 2, cx = x + rx, by = y + h;
          if (top > y + 0.01) {
            // cut the dome horizontally at 'top': compute x-intersections on ellipse
            var t = (by - top) / h; // remaining height ratio
            var half = rx * Math.sqrt(Math.max(0, 1 - Math.pow(1 - t, 2)));
            // approximate cut dome as polygon
            var pts = [], N = 24;
            for (var i = 0; i <= N; i++) {
              var a = Math.PI - (Math.PI * i / N);
              var px = cx + rx * Math.cos(a), py = by - h * Math.sin(a);
              if (py < top) py = top;
              pts.push([px * S, py * S]);
            }
            var lines = []; for (var j = 1; j < pts.length; j++) lines.push([pts[j][0] - pts[j - 1][0], pts[j][1] - pts[j - 1][1]]);
            doc.lines(lines, pts[0][0], pts[0][1], [1, 1], 'F', true);
          } else {
            doc.lines([[0, -h * k * S, rx * (1 - k) * S, -h * S, rx * S, -h * S], [rx * k * S, 0, rx * S, h * (1 - k) * S, rx * S, h * S]], x * S, by * S, [1, 1], 'F', true);
          }
        } else if (o.type === 'image') {
          var src = (o.key === 'coverPhoto' && coverImgData) ? coverImgData : E.images[o.key];
          if (!src) return;
          var fmt = /^data:image\/png/.test(src) ? 'PNG' : 'JPEG';
          doc.addImage(src, fmt, o.x * S, o.y * S, o.w * S, o.h * S, o.key, 'FAST');
        }
      });
    });
    return doc;
  };

  global.SaaamaEngine = E;
})(typeof window !== 'undefined' ? window : this);
