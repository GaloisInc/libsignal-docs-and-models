#!/usr/bin/env python3
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

DECL_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)?(noncomputable def|def|lemma|theorem)\s+([^\s(\[{:]+)")

SKIP_RE = re.compile(
    r"^(variable|open|set_option|section|noncomputable section|import|end|instance|structure|abbrev)"
)


def parse(path):
    lines = (ROOT / path).read_text().splitlines()
    ns_stack = []
    results = []
    doc = None
    in_doc = False
    doc_lines = []
    for ln in lines:
        s = ln.strip()
        if in_doc:
            if s.endswith("-/"):
                doc_lines.append(s[:-2].rstrip())
                doc = "\n".join(doc_lines).strip()
                in_doc = False
            else:
                doc_lines.append(ln.rstrip())
            continue
        if s.startswith("/--"):
            body = s[3:]
            if body.endswith("-/"):
                doc = body[:-2].strip()
            else:
                doc_lines = [body.strip()]
                in_doc = True
            continue
        m = re.match(r"^namespace\s+([\w.]+)", s)
        if m:
            ns_stack.append(m.group(1))
            continue
        m = re.match(r"^end\s+([\w.]+)", s)
        if m and ns_stack and ns_stack[-1] == m.group(1):
            ns_stack.pop()
            continue
        m = DECL_RE.match(ln)
        if m:
            kind, name = m.group(1), m.group(2)
            if name.startswith("_root_."):
                full = name[len("_root_."):]
            else:
                full = ".".join(ns_stack + [name]) if ns_stack else name
            results.append((kind, name, full, doc))
            doc = None
        elif s and not s.startswith("--") and not s.startswith("omit") and not s.startswith("/-"):
            if SKIP_RE.match(s):
                doc = None
    return results


COPYRIGHT = """/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
"""

HEADER = """import Verso
import VersoManual
import VersoBlueprint
import PQXDHDocs.Visuals.GameBoxes
import PQXDHDocs.Visuals.AnchorPill
{imports}

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option verso.docstring.allowMissing true
set_option verso.blueprint.foldCodeBlocks true
set_option doc.verso true

#doc (Manual) "{title}" =>

:::group "{group}"
{group_desc}
:::

*This chapter is AI-generated.* {notice}

"""

USES_OVERRIDE = {
    "transcriptBundle": ["spec_uake"],
    "transcriptStart": ["spec_uake"],
    "oracleBundles": ["spec_uake"],
    "challengeBundle": ["spec_uake"],
    "honestBundle": ["spec_uake"],
    "pqpkGuessed": ["spec_uake"],
    "advantage_le_forgeProb_add_indistAdvantage":
        ["spec_lemma_forgeProb", "spec_lemma_indistAdvantage", "uake_exp"],
    "forgeProb_le_sigForge_add_pqpkGuessed_add_forgeHonestGood":
        ["spec_lemma_forgeProb", "spec_lemma_sigForgeProb", "spec_lemma_pqpkGuessedProb",
         "spec_lemma_forgeHonestGoodProb"],
    "sigForgeProb_le_sig": ["spec_lemma_sigForgeProb", "spec_parameters"],
    "pqpkGuessedProb_le": ["spec_lemma_pqpkGuessedProb", "spec_parameters"],
    "forgeHonestGoodProb_le_gap":
        ["spec_lemma_forgeHonestGoodProb", "spec_ddh", "spec_security_defs"],
    "indistAdvantage_le_gap":
        ["spec_lemma_indistAdvantage", "spec_ddh", "spec_security_defs"],
    "forgeHonestGoodProb_le_pq":
        ["spec_lemma_forgeHonestGoodProb", "spec_security_defs"],
    "indistAdvantage_le_pq":
        ["spec_lemma_indistAdvantage", "spec_security_defs"],
}

PAGES = [
    {
        "out": "docs/PQXDHDocs/Chapters/Spec/Lemmas.lean",
        "title": "PQXDH Specification Lemmas",
        "group": "spec_lemmas",
        "group_desc": "The supporting-lemma layer for the Spec-model theorems.",
        "imports": ["PQXDH.Spec.UAKE.CorrectnessLemmas", "PQXDH.Spec.UAKE.WellFormedLemmas",
                    "PQXDH.Spec.UAKE.SecurityLemmas"],
        "notice": ("It surfaces the supporting-lemma layer of the Spec model (the `*Lemmas.lean` "
                   "files, whose contents are AI-written) in the blueprint: every declaration "
                   "appears as its own node, so the blueprint statistics count each supporting "
                   "lemma individually. The prose is drawn from the doc comments in those files."),
        "sections": [
            ("Correctness lemmas",
             "Probability-to-support reductions, round-trip facts for the abstract primitives, "
             "and characterizations of the support of an honest protocol run, supporting the "
             "correctness theorems.",
             "PQXDH/Spec/UAKE/CorrectnessLemmas.lean", ["spec_uake"]),
            ("Well-formedness lemmas",
             "Outputs-only-at-completion facts for the party state machines and transcript-length "
             "facts for honest runs, supporting the well-formedness theorems.",
             "PQXDH/Spec/UAKE/WellFormedLemmas.lean", ["spec_uake"]),
            ("Security games and events",
             "The challenge-phase game shared by the security hops, the derived experiments "
             "(forgery, signature forgery, KEM-key guessing, and the coin-flipped "
             "indistinguishability experiment), and the transcript-level event predicates they "
             "use.",
             "PQXDH/Spec/UAKE/SecurityLemmas/Games.lean", ["spec_uake", "uake_exp"]),
            ("Shared security hops",
             "Hops 1 through 4 of the security proofs, used by both the DH and the PQ security "
             "theorems: the forgery/indistinguishability split, the union bound over forgery "
             "causes, the SUF-CMA reduction, and the KEM public-key guessing bound.",
             "PQXDH/Spec/UAKE/SecurityLemmas/SharedHops.lean", []),
            ("GapDH core hops",
             "Hops 5 and 6 of the DH security theorem: the forgery and indistinguishability "
             "cores, against GapDH, the KDF, and the AEAD. These statements are believed true in "
             "the current model, but the standard reductions require the KDF to be a programmable "
             "random oracle, so their proofs are deferred to that planned model change; the "
             "intended sub-hops are recorded in the statements' documentation.",
             "PQXDH/Spec/UAKE/SecurityLemmas/DHHops.lean", []),
            ("IND-CCA core hops",
             "Hops 5 and 6 of the PQ security theorem: the forgery and indistinguishability "
             "cores, against the KEM's IND-CCA security, the KDF, and the AEAD. Unlike the GapDH "
             "cores, these reductions are expressible in the current model; the proofs are "
             "deferred as future reduction work.",
             "PQXDH/Spec/UAKE/SecurityLemmas/PQHops.lean", []),
        ],
    },
    {
        "out": "docs/PQXDHDocs/Chapters/Aeneas/SimplifiedLemmas.lean",
        "title": "Simplified Extraction Lemmas",
        "group": "aeneas_simplified_lemmas",
        "group_desc": "The supporting-lemma layer for the simplified extraction's theorems.",
        "imports": ["PQXDH.Aeneas.Simplified.UAKE.CorrectnessLemmas",
                    "PQXDH.Aeneas.Simplified.UAKE.WellFormedLemmas",
                    "PQXDH.Aeneas.Simplified.UAKE.SecurityLemmas"],
        "notice": ("It surfaces the supporting-lemma layer of the simplified extraction (the "
                   "`*Lemmas.lean` files, whose contents are AI-written) in the blueprint: every "
                   "declaration appears as its own node, so the blueprint statistics count each "
                   "supporting lemma individually. The prose is drawn from the doc comments in "
                   "those files."),
        "sections": [
            ("Correctness lemmas",
             "Supporting lemmas for the correctness theorems, characterizing the support of an "
             "honest run of the extracted scheme.",
             "PQXDH/Aeneas/Simplified/UAKE/CorrectnessLemmas.lean",
             ["aeneas_simplified_protocol", "spec_protocol"]),
            ("Well-formedness lemmas",
             "Unconditional outputs-only-at-completion facts for the four extracted parties, and "
             "the `toSpec` simulation lemmas for the 2-round (NoConfirm) parties, which the "
             "security lemmas do not cover.",
             "PQXDH/Aeneas/Simplified/UAKE/WellFormedLemmas.lean", ["aeneas_simplified_model"]),
            ("Security lemmas",
             "The bridge from the extracted scheme to the Spec model: under the clean-group "
             "model, each extracted party simulates its Spec counterpart, and the UAKE advantage "
             "transports along the simulation.",
             "PQXDH/Aeneas/Simplified/UAKE/SecurityLemmas.lean",
             ["aeneas_simplified_security_defs"]),
        ],
    },
    {
        "out": "docs/PQXDHDocs/Chapters/Aeneas/FullLemmas.lean",
        "title": "High-fidelity Extraction Lemmas",
        "group": "aeneas_full_lemmas",
        "group_desc": "The supporting-lemma layer for the high-fidelity extraction's theorems.",
        "imports": ["PQXDH.Aeneas.Full.UAKE.CorrectnessLemmas",
                    "PQXDH.Aeneas.Full.UAKE.WellFormedLemmas",
                    "PQXDH.Aeneas.Full.UAKE.SecurityLemmas"],
        "notice": ("It surfaces the supporting-lemma layer of the high-fidelity extraction (the "
                   "`*Lemmas.lean` files, whose contents are AI-written) in the blueprint: every "
                   "declaration appears as its own node, so the blueprint statistics count each "
                   "supporting lemma individually. The prose is drawn from the doc comments in "
                   "those files."),
        "sections": [
            ("Correctness lemmas",
             "Supporting lemmas for the correctness theorems, characterizing the support of an "
             "honest run of the extracted scheme, and deriving completeness of the extracted "
             "signature scheme from the assumptions.",
             "PQXDH/Aeneas/Full/UAKE/CorrectnessLemmas.lean",
             ["aeneas_full_protocol", "spec_protocol"]),
            ("Well-formedness lemmas",
             "Unconditional outputs-only-at-completion facts for the four extracted parties, and "
             "the `toSpec` simulation lemmas for the 2-round (NoConfirm) parties, which the "
             "security lemmas do not cover.",
             "PQXDH/Aeneas/Full/UAKE/WellFormedLemmas.lean", ["aeneas_full_model"]),
            ("Security lemmas",
             "The bridge from the extracted scheme to the Spec model: under the clean-group and "
             "KEM-pairing models, each extracted party simulates its Spec counterpart, and the "
             "UAKE advantage transports along the simulation.",
             "PQXDH/Aeneas/Full/UAKE/SecurityLemmas.lean", ["aeneas_full_security_defs"]),
        ],
    },
]

PREFIX = {
    "spec_lemmas": "spec_lemma",
    "aeneas_simplified_lemmas": "simplified_lemma",
    "aeneas_full_lemmas": "full_lemma",
}


def emit_nodes(out, path, prefix, parent, base_uses):
    for kind, name, full, doc in parse(path):
        node_kind = "definition" if "def" in kind else "theorem"
        short = name.split(".")[-1]
        anchor = f"{prefix}_{short}"
        text = re.sub(r"^\s+", "", (doc or "").strip(), flags=re.M)
        uses = USES_OVERRIDE.get(short, base_uses)
        out.write(f':::defTitle "{anchor}" "`{short}`"\n:::\n\n')
        out.write(f'::::{node_kind} "{anchor}" (parent := "{parent}") (lean := "{full}")\n')
        out.write(text + "\n")
        if uses:
            pills = " · ".join(f'{{uses "{u}"}}[]' for u in uses)
            out.write("\n{usesLabel}`uses` " + pills + "\n")
        out.write("::::\n\n")


def main():
    for page in PAGES:
        with open(ROOT / page["out"], "w") as out:
            out.write(COPYRIGHT)
            out.write(HEADER.format(
                imports="\n".join(f"import {m}" for m in page["imports"]),
                title=page["title"], group=page["group"], group_desc=page["group_desc"],
                notice=page["notice"]))
            for title, intro, path, base_uses in page["sections"]:
                out.write(f"# {title}\n\n{intro}\n\n")
                emit_nodes(out, path, PREFIX[page["group"]], page["group"], base_uses)
        print(page["out"])


if __name__ == "__main__":
    main()
