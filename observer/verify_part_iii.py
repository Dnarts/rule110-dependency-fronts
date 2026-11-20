"""Recount Paper II.3's frozen dev observations. Reads JSON only; no inference."""
import hashlib
import json
import math
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parent
LETTERS = (362, 426)
BITS = (15, 16)
MIDDLES = sorted((f"{i:06b}" for i in range(64)),
                 key=lambda u: hashlib.sha256(("observer-v2|" + u).encode("ascii")).digest())[:8]
WORDS = [l + u + r for u in MIDDLES for l, r in product("01", repeat=2)]
GRID = {(x, h, e) for x, h, e in product(WORDS, "AB", (0, 1))}
EXPECTED = {
    "g1-dev-base-01": ("FAIL_DEV", 76, 0, 0),
    "g1-dev-instruct-aligned-02": ("FAIL_FORMAT", 79, 0, 1),
    "g1-dev-instruct-chat-03": ("FAIL_DEV", 115, 2, 9),
    "g1-dev-instruct-switch-04": ("FAIL_DEV", 109, 0, 6),
    "two-step-instruct-chat-04": ("PASS_DEV", 124, 6, 16),
}


def check(ok, field):
    if not ok:
        raise ValueError(field)


def load(name):
    return json.loads((ROOT / name / "report.json").read_bytes())


def check_grid(rows):
    check(len(rows) == 128 and {(r["x"], r["h"], r["e"]) for r in rows} == GRID, "dev grid")
    check(all(r["u"] == r["x"][1:-1] for r in rows), "middle")


def pred(obs, tokens):
    a, b = obs["logits"]
    p, q = obs["probabilities"]
    check(all(map(math.isfinite, (a, b, p, q))) and 0 <= min(p, q) <= max(p, q) <= 1,
          "non-finite or invalid token observation")
    check(b - a == obs["margin"] and p + q == obs["mass"], "margin or token mass")
    winner = None if a == b else int(b > a)
    check(winner == obs["pred"], "binary decision")
    if winner is not None and obs["mass"] >= 0.8:
        check(obs["greedy_id"] == tokens[winner], "full-vocabulary winner")
    return winner


def check_replay():
    d = load("g0r-base-01")
    check(d["g0"]["status"] == d["g0r"]["status"] == "PASS", "G0/G0R verdict")

    def equal(a, b, proof):
        check(a == b and a["shape"] == [100278] and a["dtype"] == "mlx.core.bfloat16"
              and proof["sha256"] == a["sha256"] and a["nbytes"] == proof["checked_bytes"] == 200556
              and proof["native_bytes_equal"] is True and proof["max_abs_diff"] == 0.0,
              "recorded native logit comparison")

    for h in "AB":
        control = d["g0"]["rows"][h]
        equal(control["before"], control["after"], control["comparison"])
    rows = d["g0r"]["rows"]
    check_grid(rows)
    for r in rows:
        check(r["donor"] in "AB" and r["donor"] != r["h"], "opposite donor")
        equal(r["midpoint"], r["natural_donor"], r["mid_check"])
        equal(r["end"], r["natural_recipient"], r["end_check"])
    check(2 * len(rows) == d["g0r"]["full_logit_comparisons"] == 256, "G0R denominator")
    print("G0 PASS; G0R 256/256 reported byte matches, max_abs_diff=0.0")


def check_chat_diagnostics(d):
    recall = d["diagnostics"]["recall"]
    check(len(recall) == 2 and {r["h"] for r in recall} == {"A", "B"}, "D1 grid")
    for r in recall:
        check(pred(r, LETTERS) == int(r["h"] == "B") and r["mass"] >= 0.8, "D1")
    rows = d["diagnostics"]["explicit_rule"]
    check(len(rows) == 64 and {(r["x"], r["p"]) for r in rows} == set(product(WORDS, range(2))), "D3 grid")
    scores = {}
    for r in rows:
        x, rule = r["x"], r["p"]
        target = int((x[0], x[-1])[rule])
        scores[x, rule] = pred(r, BITS) == target
        check(r["target"] == target and r["correct"] == scores[x, rule] and r["mass"] >= 0.8, "D3 row")
    blocks = sum(all(ok for (x, _), ok in scores.items() if x[1:-1] == u) for u in MIDDLES)
    check(sum(scores.values()) == 62 and blocks == 6 and
          all(d["diagnostic_status"][name]["status"] == "PASS_DEV" for name in ("D1", "D3")), "D1/D3 verdicts")


def check_relay(d):
    senders = d["senders"]
    check([(r["h"], r["e"]) for r in senders] == list(product("AB", (0, 1))), "sender grid")
    table = []
    for r in senders:
        bit = pred(r, LETTERS)
        check(bit is not None and r["accepted"] and r["greedy_unique"]
              and r["mass"] >= 0.8 and r["greedy_id"] == r["delivered_id"], "sender")
        table.append(bit)
    check(table == [0, 1, 1, 0] and d["summary"]["sender_table"] == "0110", "one-bit code")
    controls = {(r["x"], r["p"]): r for r in d["recipient_controls"]}
    check(len(d["recipient_controls"]) == 64 and set(controls) == set(product(WORDS, range(2))), "receivers")
    erased = delivered = different = 0
    for r in d["rows"]:
        x = r["x"]
        bit = table[2 * int(r["h"] == "B") + r["e"]]
        check(r["delivered_id"] == LETTERS[bit] and r["recipient"] == controls[x, bit], "delivered control")
        constant = controls[x, 0]
        check(constant["letter_id"] == LETTERS[0] and constant["accepted"] and constant["mass"] >= 0.8,
              "constant A")
        correct = pred(constant, BITS) == r["target"]
        check(correct == r["erased_correct"], "erased correctness")
        if x[0] != x[-1]:
            different += 1
            erased += correct
            delivered += r["correct"]
    check((delivered, erased, different) == (64, 32, 64), "differing-end erasure control")
    print("relay 0110; delivered 64/64, constant A 32/64 on differing ends")


def check_condition(name, expected):
    d = load(name)
    rows = d["rows"]
    check(d["heldout_run"] is False and d["dev_middles"] == MIDDLES, "dev provenance")
    check_grid(rows)
    scores = {}
    for r in rows:
        x, h, e = r["x"], r["h"], r["e"]
        target = int((x[0], x[-1])[int(h == "B") ^ e])
        obs = r.get("recipient", r)
        correct = pred(obs, BITS) == target
        check(obs["mass"] >= 0.8 and r["target"] == target and r["correct"] == correct, "primary row")
        scores[x, h, e] = correct
    blocks = sum(all(ok for (x, _, _), ok in scores.items() if x[1:-1] == u) for u in MIDDLES)
    wrong_pairs = sum(all(scores[x, h, 1] for h in "AB") for x in WORDS if x[0] != x[-1])
    if "senders" in d:
        check_relay(d)
        format_failures = 0
    else:
        explicit = d["diagnostics"]["explicit_rule"]
        check(len(explicit) == 64, "explicit grid size")
        format_failures = sum(r["mass"] < 0.8 for r in explicit)
        check(format_failures == (28 if name == "g1-dev-instruct-aligned-02" else 0), "explicit format")
    verdict = "FAIL_FORMAT" if format_failures else ("PASS_DEV" if blocks >= 6 else "FAIL_DEV")
    check((verdict, sum(scores.values()), blocks, wrong_pairs) == expected and d["status"] == verdict, name)
    if name == "g1-dev-instruct-chat-03":
        check_chat_diagnostics(d)
        print("native chat D1 2/2; D3 62/64, 6/8 blocks")
    print(f"{name}: {verdict}, {sum(scores.values())}/128, {blocks}/8 blocks, {wrong_pairs}/16 wrong pairs")


def check_frozen_contract():
    # The five historical runs hashed the contract before series navigation existed.
    nav, separator, original = (ROOT / "gate_contract_ru.md").read_bytes().partition(b"\n\n")
    check(separator and len(nav.splitlines()) == 5 and
          all(line.startswith(b"> **") for line in nav.splitlines()), "contract navigation boundary")
    digest = hashlib.sha256(original).hexdigest()
    for name in ("g0r-base-01", *EXPECTED):
        report = load(name)
        if name == "two-step-instruct-chat-04":
            manifest = ROOT / "two-step-interface-04.json"
            check(hashlib.sha256(manifest.read_bytes()).hexdigest() == report["manifest_sha256"],
                  "two-step interface differs from the measured interface")
        else:
            check(report["inputs"]["gate_contract_ru.md"] == digest, "historical contract: " + name)


if __name__ == "__main__":
    check_frozen_contract()
    check_replay()
    for condition, expected_result in EXPECTED.items():
        check_condition(condition, expected_result)
