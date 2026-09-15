#!/usr/bin/env python3
"""Regenerate the machine-derived tables of work/FINAL_REVIEW_DRAFT.md.

Usage (from the package root, after `bash work/delivery/refresh.sh`):
    python3 work/delivery/tools/gen_final_review_tables.py              # print tables
    python3 work/delivery/tools/gen_final_review_tables.py --write      # rewrite the marked
                                                                        # sections of work/FINAL_REVIEW_DRAFT.md
Sources: tools/claims.py --json (claim numbering and counts), work/lean/lean-declarations.json
(row status, declaration, module, review file), work/delivery/receipts/declaration-audit.summary.json
(axioms per mapped declaration; falls back to the live work/checks/declaration-audit.json),
work/reviews/<row>.json (verdict, disclosed readings). It runs no Lean tool and no checker.
The prose between the markers is not touched; only the tables between
<!-- BEGIN:NAME --> / <!-- END:NAME --> are replaced.
"""
import json, os, re, subprocess, sys, collections, datetime

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..'))
WORK = os.path.join(ROOT, 'work')
DRAFT = os.path.join(WORK, 'FINAL_REVIEW_DRAFT.md')

AX_ABBR = {'propext': None, 'Classical.choice': None, 'Quot.sound': None,
           'SM.lit_homfly': 'H', 'SM.lp_lm': 'LM', 'SM.lp_lm_uniqueness': 'LMU', 'SM.ng_finite_word': 'NG'}
LABEL_RE = re.compile(r'\b(FR-[A-Z]{0,3}-?\d+|CE-R\d+|D-F\d+|D-ER\d+|D-FR\d+|D-CP-\d+|D-\d\b|K-\d+|GAP-\d|F4|D2\b|D9\b)')

# Hand-curated one-clause readings for the rows the review must single out. Everything else is
# derived from the review file (labels + first disclosed note).
CURATED = {
 'lem:shift': 'proved as printed on SM15 (clause (iii) with −z(P), clause (iv) on the regular locus); SM12 counterexample work/repairs/ShiftZeroTurn.lean documents the erratum (scope_issue/sm15_note in the map); cold-start review 2026-09-12 + countersignature',
 'lem:chi-basic': 'handover review + countersignature 2026-09-13; SM15 wording-only change (left/right naming convention) re-read and countersigned (source_realignment.re_review)',
 'lem:g1': 'handover review + countersignature 2026-09-13; SM15 clause (iv) "two distinct adjacent edges" — SM.g1 already states i ≠ j (re_review countersigned)',
 'prop:A-chamber': 'handover review + countersignature 2026-09-13; SM15 "constant on every labelled chamber (the root fixed)" = the labelled-chamber conjunct of SM.A_chamber (re_review countersigned)',
 'ng:front-domain': 'FR-1 polygonal reading of S(F) (S is a Diagram carrying the Marking of the rounded curve G); FR-2 cusp criterion in derivative form; FR-3/FR-4 smooth = C^∞, 1-periodic parameter circles',
 'ng:smoothing-record': 'FR-1/D-F6: IsRounding S does not tie S to the rounded curves G; printed content kernel-checked as library thm SM/FrontGeomModel.lean isRounding_of_geomModel (cited, not a row)',
 'ng:circle': 'FR-8 class narrowing: sentence 1 on realizations of closed oriented Rutherford words (SM.realize), sentence 2 on PLFront (FR-11); FR-5 word layer is the printed certificate device',
 'ng:cusp-skein': 'FR-8 stated on SM.realize of closed oriented words; FR-12 unique compatible smoothing as a theorem, right-cusp templates outside the row',
 'ng:finite-word': 'literature axiom stated on closed oriented words (FR-6): PrincipalChain stop rule as a consequence of Laws; empty word included (trivial)',
 'ce:rounding': 'CE-R1 diagram = RegularGenericProjection (no polygonal Diagram delivered); CE-R2 ℝ-indexed SpatialFamily via the smoothTransition time clamp; CE-R4 construction constants differ (statement unaffected)',
 'ce:smoothing-record': 'D-1 collar field on CleanCuspSmoothing; K-3 D_ε fields quantify over CuspRoundingFamily; K-5 clean neighbourhood convex (IsDisc); FR-1 polygonal reading',
 'cf:lem-rounding': 'FR-R1 D_ε = polygonal D carried by the smooth curve (Carried record); FR-R3 no_triple via PolygonDiagram.generic; FR-R4 period-1 parameter; witness exports more than printed',
 'cf:lem-curl': 'FR-C1 record-level carrying (RecordCarried, no τ_eval at the kink); FR-C2 disc inside any preassigned neighbourhood (stronger); FR-C4 P_{F\'} = P_F via polygonal RI',
 'cb:embedded-rotation': 'D-ER1 proved independently of deferred row 57; FR-ER-2 sign read at supporting vertices (bounded region not defined); Embedded P wider than generic m = 0',
 'fd:linking-calculus': 'D-F16 restated unconditionally (RegularPoleCount proved); framing pushoff embeddedness not asserted (printed sentence claims disjointness only)',
 'fd:transverse-neighborhood': 'FR-TN-3 no smoothness field for h (forced); FR-TN-5 TransverselyIsotopic endpoints; one false internal leaf repaired without statement change',
 'fd:generic-front': 'D-F15 compact support inside IsContactIsotopy = disclosed strengthening; FR-GF-1..8',
 'fd:contact-motions': 'SmoothDependence proved inside the module (D-F13 superseded); unconditional',
 'fd:parameter-avoidance': 'FR-PA-1 K compact in EuclideanSpace ℝ (Fin d), not an abstract manifold',
 'def:transverse-front': 'contact space, C^∞ 1-periodic embedded loops, z′ − y x′ > 0; RegularGenericProjection is "the diagram" (GAP-1: no polygonal record built here)',
 'CV:ax:gausscode': 'F4 replacement (scope change recorded AUTHOR_NOTES ~01:24Z): conclusion homfly D = homfly D′ instead of "present the same oriented link"; strictly weaker; all consumers pass through polynomial equality',
 'CV:ax:homfly': 'DERIVED (theorem, not axiom) from SM.lit_homfly/lp_lm/lp_lm_uniqueness; D2: links = LinkEquiv classes of polygonal diagrams',
 'CV:ax:R': 'CV.hyp_R is a Prop definition (the hypothesis) in the R6 all-sides chamber-value form; hn : 3 ≤ n presupposition',
 'CV:lem:carrierword': 'binder NARROWED to diagrammatic polygons and iterated carriers (round-2 unanimous; content-preserving on every instance the source uses)',
 'CV:lem:carriers': '(ii) ranges over marked points of Γ only (finite carrier model); double points via accepted def:interlace',
 'lit:homfly': 'polygonal Diagram domain (def:positive-lift reading); planar isotopy = EqvGen(Reparam ∨ Deform); descent over LinkEquiv (D2); skein triples = switch-and-smooth (D3)',
 'lp:lm': '∃-form for "the function constructed in LM §1"; witness lmF pinned by lp:lm-uniqueness; polygonal domain',
 'lp:lm-uniqueness': 'competitor hypothesis Q = 1 on every crossing-free one-component polygon (formally stronger hypothesis, no effect)',
 'def:positive-lift': 'Diagram is a labelled presentation (base vertex, component order) of the printed diagram; polygonal class (sm-3:337-343)',
 'def:gauss-record': 'domain = polygonal generic diagrams (regular smooth immersions of the bridge paragraph not in the class)',
 'mp:blocks': 'D9: clean marked join = RecordIso to joinRecord; sign_preserved as an abstract bijection; realizes clause kept and proved',
 'cb:blocks': 'R-1..R-12: SM block = accepted CV.Piece; owner defined via a fixed visit and pinned; hn : 3 ≤ n bundle parameter',
 'cb:products': 'R-4/R-5: D_H = positiveLift of a carrier of an independent refinement; P_H = recordPolynomial of the restricted record',
 'thm:C-S3': 'side values below an existential δ with τ_j = ∓1 over both Booleans (equivalent to chamber values by def:germ + prop:C-chamber); n ≥ 4 via N = n+1',
 'thm:C-S5': 'conclusion on the germ\'s own no-loop side points P(t), t in the side interval (chamber values via prop:C-chamber)',
 'prop:C-chamber': 'quantified over labelled representatives with polygonProjection Q ∈ chamber (polygonProjection P); entails cyclic-relabelling invariance (printed content made explicit)',
 'prop:C-silent': 'design B/R2 hybrid (work/drafts/csilent/PLAN_FINAL.md); exterior-extension (E) and pure-cut (C) walls as printed',
 'R:generic_selector': 'fixed labels a = x_ef, b = x_eg, c = x_fg with the canonical branch + relabelled instances; sides named by local graphs; ownership convention kernel-checked (mixed_carrier was FALSE in design B)',
 'R:generic_transport': 'G11 RIII-wall invariance proved by an explicit polygonal RIII move; hs crossing-set identification a universally quantified hypothesis of cross-wall fields',
 'R:exterior': 'exterior factor represented by the base row; printed full-availability binder kept',
 'R:availability_0_1': 'summand_transport stronger than the bare fibre identity; cross-wall fields presuppose hs',
 'R:localization': 'corollary sentence 2 ("both orbits occur") omitted by executor decision (consumed by nothing)',
 'R:parity': 'avail_wall_invariant conditional on the cross-wall support identification hs (R-LOC-2 (1))',
 'R:fibre_partition': 'X₁-free form of the partition identity for every support (the complete def:X1 summand identity lives in the X₁ rows)',
 'R:generic_table': 'words/tables asserted on the canonical branch s_a = s_b = s_c (relabelled instances by F2(A))',
 'Bridge:B4': 'the C = X₁ dictionary through the accepted geo*_eq_generic lemmas (CV-DOM option (C))',
 'Bridge:B2': 'stated under sorted naming rep e < rep f < rep k; unsorted case via exists_sorted_tripleAt',
 'conv:selected-visits': 'finite successor model of the source proof over the ported Carrier lane',
 'def:smoothing': 'continuum traversal circle replaced by the finite marked circle (Mark P); cycles as successor orbits',
 'lem:carriers': '(i) "independent of the order of reconnections" has no propositional counterpart (carriers defined directly as cycles)',
 'def:soft': 'labelling of P_ε pinned only through bijectivity and cyclic successor relations',
 'thm:uniqueness': 'formally weaker-or-equal hypotheses (theorem at least as strong)',
 'lem:weak-open': 'extra supporting lemma outside the 132 (scope_note in the map)',
}

# Reasons for pending rows (executor: update the "in progress" lines at the end).
PENDING_REASONS = {
 'lem:gauss-two-discs': 'DEFERRED — PL Jordan–Schoenflies on S²; judged INFEASIBLE now (12-20k lines, no Mathlib Jordan/Euler/triangulations): work/drafts/pldiscs/PLDISCS_FEASIBILITY.md §2.4; only non-GAP-2 consumer (row 104) proved without it (D-ER1). AUTHOR_NOTES 2026-09-13 ~20:55Z, 2026-09-14 ~04:38Z, ~12:45Z',
 'ng:commutation': 'IN PROGRESS at draft time — certificate rows lane / sweep (`represent`, U8R SweepStatement); statement fixed in work/drafts/frontrows/Statements_FINAL.lean; FR-8 (D-F7)',
 'ng:front-I': 'IN PROGRESS at draft time — certificate rows wave 3a (U6 typeI_move); statement fixed in work/drafts/frontrows/Statements_FINAL.lean',
 'ng:front-II': 'IN PROGRESS at draft time — certificate rows wave 3a (U6 typeII_move)',
 'ng:front-III': 'IN PROGRESS at draft time — certificate rows wave 3a (U5 typeIII_site done, merger pending)',
 'ng:deletions': 'IN PROGRESS at draft time — certificate rows wave 3a (U6 crossedCusp_move)',
 'ng:local-front-bound': 'IN PROGRESS at draft time — proved on words inside the skeleton; accepted only together with row 76 (`represent`), FR-8/D-F7',
 'cp:finite-contact-path': 'GAP-2 — proved modulo one named clause (see §3.1 paragraph); library module SM/ContactPathOfDescent.lean, never mapped (D-F11)',
 'src:contact': 'NEVER DECLARED — literature interface consumed only by fd:contact (94) and CV:ax:etnyre (161), both GAP-2-blocked (blueprint/DEPENDENCIES.json edges); no consumer can cite it, so it was not stated (5th of the five admitted interfaces; policy name SM.src_contact)',
 'fd:ng-bound': 'IN PROGRESS at draft time — waits on row 83 (restates it in self-linking form; architect NgBound_Statement.lean / NGBOUND_PLAN.md)',
 'fd:contact': 'GAP-2 via row 91 (and the undeclared src:contact interface)',
 'cf:thm-carrierfloor': 'GAP-2 — clauses (R)(A)(B) statable/provable, clause (C) blocked via fd:contact (94) (GAP-2 memo §3(c); D-F12: partial clauses not pursued)',
 'thm:floor': 'GAP-2 — z_parity provable, a_floor blocked via cf:thm-carrierfloor (C)',
 'cb:singleton': 'GAP-2 via thm:floor',
 'lem:corner-values': 'GAP-2 via cb:singleton (clause (ii)); clause (i) also cites deferred row 57',
 'thm:C-S7': 'GAP-2 via cb:singleton / thm:floor — target row, fixed name SM.thm_C_S7 not declared (D-F11)',
 'thm:C-soft': 'GAP-2 via lem:corner-values — target row, fixed name SM.thm_C_soft not declared (D-F11)',
 'hyp:R': 'NOT STATED — SM hypothesis row (axiom-policy mode explicit_parameter, fixed name SM.hyp_R); its only consumers thm:comparison (GAP-2) and Bridge:theorem (blocked) are open. Statable now like CV:ax:R; see §7',
 'prop:anchor-values': 'GAP-2 via thm:C-soft',
 'thm:comparison': 'GAP-2 via lem:corner-values / thm:C-S7 / thm:C-soft — fixed name SM.thm_comparison not declared; also consumes hyp:R (explicit parameter)',
 'cor:C-inherits': 'GAP-2 via thm:comparison — fixed name SM.cor_C_inherits not declared',
 'CV:thm:carrierfloor': 'GAP-2 — (R)(A)(B)(C) through the polygon bridge, (D) provable now; blocked via CV:ax:slbound → fd:contact (memo §3(c))',
 'CV:ax:etnyre': 'GAP-2 — D-F10 option (iii): no independent sl object; kept as the parametrised bundle CV.SlBoundData with 162; a sixth axiom rejected by policy',
 'CV:ax:slbound': 'GAP-2 — statable on TransverseKnot, blocked via fd:contact (memo §3(b))',
 'CV:singleton_D_i': 'GAP-2 via CV:thm:carrierfloor and cb:singleton',
 'R:generic_selected': 'GAP-2 — needs CV:thm:carrierfloor (R lane statement panel, AUTHOR_NOTES ~06:35Z); statable',
 'R:extreme_pair_zero': 'BLOCKED via CV:singleton_D_i (GAP-2); statable',
 'R:extreme_transport': 'GAP-2 — needs CV:thm:carrierfloor; statable',
 'R:extreme_selected': 'GAP-2 — needs CV:thm:carrierfloor; statable',
 'R:cv_theorem': 'BLOCKED — RProof.cv_R : CV.hyp_R needs rows 174-177; not declared (statement fixed in work/drafts/rlane2/Statements_FINAL.lean)',
 'Bridge:theorem': 'BLOCKED — Bridge.sm_R waits only for RProof.cv_R (AUTHOR_NOTES 07:33Z); not declared',
 'SM:corner_laws_and_soft': 'BLOCKED — final theorem needs Bridge:theorem, cor:C-inherits, thm:C-soft; not declared (D-F11); reported INCOMPLETE',
}

def load(p):
    with open(p) as f: return json.load(f)

def claims_json():
    out = subprocess.run([sys.executable, os.path.join(ROOT, 'tools', 'claims.py'), '--json'], capture_output=True, text=True, cwd=ROOT)
    return json.loads(out.stdout)

def audit_axioms():
    summ = os.path.join(WORK, 'delivery', 'receipts', 'declaration-audit.summary.json')
    if os.path.exists(summ):
        s = load(summ); src = 'work/delivery/receipts/declaration-audit.summary.json'
        return {d['declaration']: d['axioms'] for d in s['mapped_declarations']}, src
    a = load(os.path.join(WORK, 'checks', 'declaration-audit.json')); src = 'work/checks/declaration-audit.json'
    return {d['declaration']: d['axioms'] for d in a['audit']['declarations']}, src

def abbr(axs):
    if axs is None: return '(not audited)'
    extra = [AX_ABBR.get(a, a) for a in axs if AX_ABBR.get(a, a)]
    return 'std' + ('+' + '+'.join(extra) if extra else '')

def esc(s): return str(s).replace('|', '\\|').replace('\n', ' ')

def short(s, n=150):
    s = ' '.join(str(s).split())
    return s if len(s) <= n else s[:n-1].rstrip() + '…'

def readings(rid, rev):
    if rid in CURATED: return CURATED[rid]
    disc = rev.get('discrepancies') or []; st = rev.get('stronger_than_source') or []; wk = rev.get('weaker_than_source') or []
    cs = rev.get('countersignature_20260913')
    if not rev.get('ai_review_disclosure') and isinstance(cs, dict):
        # handover-era review (2026-09-10/11) re-reviewed by a separate session on 2026-09-13
        d2 = cs.get('notes_listed_as_discrepancies') or []; s2 = cs.get('stronger_than_source') or []; w2 = cs.get('weaker_than_source') or []
        rr = (rev.get('source_realignment') or {}).get('re_review')
        head = 'handover review + countersignature 2026-09-13 (%s)' % cs.get('verdict', '?')
        if rr: head += '; SM15 wording-change re-read countersigned'
        first = next((x for x in (w2 + d2 + s2) if x), None)
        n = len(d2) + len(s2) + len(w2)
        return head + ('; ' + short(first, 120) if first else '; no notes') + (f' [{n} note{"s" if n != 1 else ""}]' if n else '')
    labels = sorted(set(LABEL_RE.findall(json.dumps([disc, st, wk, rev.get('executor_notes', '')]))))
    first = next((x for x in (wk + disc + st) if x and not str(x).lower().startswith(('none', 'no '))), None)
    parts = []
    if labels: parts.append('labels ' + ', '.join(labels))
    if first: parts.append(short(first, 140))
    if not parts: parts.append('none disclosed (arrays empty)' if not (disc or st or wk) else 'notes marked non-blocking only')
    n = len(disc) + len(st) + len(wk)
    return '; '.join(parts) + (f' [{n} note{"s" if n != 1 else ""}]' if n else '')

def main(write=False):
    cj = claims_json(); units = cj['units']; num = {u['id']: i + 1 for i, u in enumerate(units)}
    m = load(os.path.join(WORK, 'lean', 'lean-declarations.json'))['declarations']
    idx = {r['id']: i + 1 for i, r in enumerate(m)}
    ax, axsrc = audit_axioms()
    stage = load(os.path.join(WORK, 'checks', 'stage-development.json'))
    st = {r['id']: r for r in m}
    unit_kind = {u['id']: u['unit'] for u in units}
    now = datetime.datetime.utcnow().strftime('%Y-%m-%d %H:%M UTC')

    # --- summary
    claims = [u for u in units if u['unit'] == 'claim']; defs = [u for u in units if u['unit'] == 'definition']
    others = [r for r in m if r['id'] not in num]
    def cnt(rows, key=lambda r: r['status']):
        c = collections.Counter(key(r) for r in rows); return c.get('accepted', 0), c.get('implemented', 0), c.get('pending', 0)
    rows_summary = [
        ('source claims (tools/claims.py: "claims verified")', cj['claims_total'], *cnt(claims, lambda u: st[u['id']]['status'])),
        ('definitions / conventions (units of work, not claims)', len(defs), *cnt(defs, lambda u: st[u['id']]['status'])),
        ('literature interfaces + hypotheses + extra lemma (map rows outside claims.py)', len(others), *cnt(others)),
        ('checklist rows total (work/lean/lean-declarations.json)', len(m), *cnt(m)),
    ]
    S = [f'| unit class | total | accepted | implemented (awaiting review) | pending |', '|---|---|---|---|---|']
    for name, tot, a, i, p in rows_summary: S.append(f'| {name} | {tot} | {a} | {i} | {p} |')
    tg = ["prop:C-chamber", "prop:C-silent", "thm:C-S3", "thm:C-S5", "thm:C-S7", "thm:C-soft", "Bridge:theorem", "SM:corner_laws_and_soft"]
    tga = sum(1 for t in tg if st[t]['status'] == 'accepted')
    S.append(f'| final targets (EXECUTION.json) | {len(tg)} | {tga} | 0 | {len(tg) - tga} |')
    S.append('')
    S.append(f'Generated {now} from `python3 tools/claims.py --json` (claims verified {cj["claims_verified"]}/{cj["claims_total"]}), the map and `{axsrc}`. '
             f'Current checker receipt work/checks/stage-development.json: passed={stage.get("passed")}, stage={stage.get("stage")}, stage_accepted={stage.get("stage_accepted")}, '
             f'mapped_declarations={stage.get("mapped_declarations")}, audited_declarations={stage.get("audited_declarations")}.')

    # --- accepted
    A = ['| # | row | Lean declaration | module | review file | verdict | axioms | disclosed readings (one clause) |', '|---|---|---|---|---|---|---|---|']
    for r in m:
        if r['status'] != 'accepted': continue
        rev = load(os.path.join(WORK, r['review_file']))
        n = num.get(r['id']); tag = str(n) if n else f'm{idx[r["id"]]}'
        v = str(rev.get('verdict', '')); v = 'faithful' if v.startswith('faithful') else v
        A.append(f'| {tag} | `{r["id"]}` | `{r["declaration"]}` | {r["module"]} | {r["review_file"]} | {v} | {abbr(ax.get(r["declaration"]))} | {esc(readings(r["id"], rev))} |')
    # --- pending
    P = ['| # | row | policy / fixed name | status | reason at draft time |', '|---|---|---|---|---|']
    pol = load(os.path.join(WORK, 'lean', 'axiom-policy.json'))
    fixed = dict(pol['targets']); fixed.update(pol['literature']); fixed[pol['hypothesis']['label']] = pol['hypothesis']['declaration']
    for r in m:
        if r['status'] == 'accepted': continue
        n = num.get(r['id']); tag = str(n) if n else f'm{idx[r["id"]]}'
        P.append(f'| {tag} | `{r["id"]}` | {("`" + fixed[r["id"]] + "`") if r["id"] in fixed else "—"} | {r["status"]} | {esc(PENDING_REASONS.get(r["id"], "(reason to be filled by the executor)"))} |')
    # --- R / bridge table
    Rrows = [u['id'] for u in units if u['id'].startswith(('R:', 'Bridge:', 'SM:corner'))] + ['CV:ax:R', 'hyp:R']
    R = ['| obligation | policy name | status | declared? | module | axioms | note |', '|---|---|---|---|---|---|---|']
    for rid in Rrows:
        r = st[rid]; name = fixed.get(rid, r.get('declaration') or '—')
        decl = ax.get(r['declaration']) if r['status'] == 'accepted' else None
        note = 'accepted' if r['status'] == 'accepted' else short(PENDING_REASONS.get(rid, ''), 110)
        R.append(f'| `{rid}` | `{name}` | {r["status"]} | {"yes" if r["status"] == "accepted" else "no"} | {r["module"] or "—"} | {abbr(decl) if r["status"] == "accepted" else "—"} | {esc(note)} |')

    blocks = {'SUMMARY': S, 'ACCEPTED': A, 'PENDING': P, 'RTABLE': R}
    if not write:
        for k, v in blocks.items(): print(f'<!-- BEGIN:{k} -->'); print('\n'.join(v)); print(f'<!-- END:{k} -->\n')
        return
    text = open(DRAFT).read()
    for k, v in blocks.items():
        pat = re.compile(rf'(<!-- BEGIN:{k} -->).*?(<!-- END:{k} -->)', re.S)
        if not pat.search(text): print('marker missing:', k); continue
        text = pat.sub(lambda mo: mo.group(1) + '\n' + '\n'.join(v) + '\n' + mo.group(2), text)
    open(DRAFT, 'w').write(text)
    print(f'rewrote tables in {DRAFT}: accepted {len(A)-2}, pending {len(P)-2}, R rows {len(R)-2}; {sum(1 for _ in open(DRAFT))} lines')

if __name__ == '__main__':
    main(write='--write' in sys.argv)
