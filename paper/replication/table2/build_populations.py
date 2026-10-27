"""Potential-outcome populations for Table 2: populations/pop_<item>_fpr10/15/20.npz, item = headline, pros, cons.

Sample: 4,000 Glassdoor reviews written before AI assistants (2019 to mid-2021, at most 20 per firm), split into
development employees (30 percent) and survey employees.  For each survey employee and item:
  r0, f0   code of the employee's own answer and the detector's flag on it
  r1, f1   code of an AI answer written for that employee (Gemini or DeepSeek; the employee's AI twin, written by
           Claude or GPT from the ratings alone, when none exists) and the detector's flag on it
  x        overall rating group (1-2, 3, 4-5)
The detector is a character n-gram logistic regression trained on development answers against references by
Claude and GPT, cross-fitted over five folds; its threshold flags the chosen share of development human answers.

    python3 build_populations.py            # reads ../data/, writes populations/ (about 35 s)
"""
import gzip
import hashlib
import json
import re
from collections import defaultdict
from pathlib import Path

import numpy as np
import pandas as pd
from sklearn.feature_extraction.text import TfidfVectorizer
from sklearn.linear_model import LogisticRegression

HERE = Path(__file__).resolve().parent
ITEMS = ["headline", "pros", "cons"]
THEMES = ["pay and benefits", "management and leadership", "colleagues and culture",
          "workload and work-life balance", "career and training", "other or insufficient"]
REF_MODELS = {"anthropic/claude-sonnet-5", "openai/gpt-chat-latest"}
SURVEY_MODELS = {"google/gemini-3.8-flash", "deepseek/deepseek-v4.1-flash"}

# ------------------------------------------------------------------ frozen coding rule
KEYWORDS = [
    r"\b(pay|paid|salary|salaries|wage|wages|bonus|bonuses|benefit|benefits|pension|compensation|money|perks?|discount|holidays?|annual leave|raise|rewards?)\b",
    r"\b(manage(r|rs|ment)|boss(es)?|leadership|leaders?|senior|director|executives?|ceo|supervisor|head office|hr)\b",
    r"\b(colleagues?|co-?workers?|team|teams|people|staff|culture|atmosphere|environment|friendly|friends?|supportive|community)\b",
    r"\b(hours|workload|work load|stress(ful)?|pressure|busy|overtime|shifts?|understaffed|short staffed|work[- ]life|balance|flexib(le|ility)|remote|hybrid|tiring|long days)\b",
    r"\b(career|progression|promotion|promotions|training|develop(ment)?|learn(ing)?|growth|opportunit(y|ies)|skills?|experience)\b",
]


def code_texts(texts):
    """Most-matched theme; ties go to the earlier theme; no keyword -> 'other or insufficient'."""
    out = []
    for t in texts:
        hits = [len(re.findall(p, (t or "").lower())) for p in KEYWORDS]
        out.append(int(np.argmax(hits)) if max(hits) > 0 else len(THEMES) - 1)
    return np.array(out, int)


# ------------------------------------------------------------------ cleaning of chatbot replies
_LABEL = re.compile(r"^(?:option|version|draft|alternative)\s*\d+\b", re.I)
_FIELD = re.compile(r"^(?:my\s+)?(?:headline|answer|response|review)\s*:\s*", re.I)
_CLOSING = re.compile(r"^\(?\s*(?:note|tip)\b|^(?:feel free|let me know|would you like|i hope|hope this|"
                      r"if you(?:'d| would)? (?:like|prefer|want)|you (?:can|could) (?:also|adjust|tweak|add|swap|"
                      r"change|use|try|go)|this (?:keeps|version|captures|strikes|sounds|wording|phrasing)|"
                      r"(?:pick|choose) (?:whichever|the one|one))", re.I)
_META = re.compile(r"\b(?:let me know|feel free|would you like|i can (?:adjust|help|tweak|rewrite|make))\b", re.I)
_BULLET = re.compile(r"^(?:[-*•]|\d+[.)])\s+")
_QUOTED = re.compile(r'^["“](.*)["”]$', re.S)


def _plain(line):
    return re.sub(r"\*\*|__", "", re.sub(r"^\s*(?:#+|>)\s*", "", line)).strip()


def _label_content(line):
    m = re.match(r"^\s*>?\s*\*\*(.+?)\*\*\s*:?\s*(.*)$", line)
    if m:
        return m.group(2).strip()
    m = re.match(r"^[^:]*:\s*(.*)$", _plain(line))
    return m.group(1).strip() if m and len(m.group(1).split()) >= 6 else ""


def as_pasted(text):
    """The answer a respondent would paste from a chatbot reply: first draft only, without introduction,
    draft labels, list markers, quotes, markdown, or closing offers to revise."""
    lines = (text or "").strip().split("\n")
    marks = [i for i, l in enumerate(lines) if _plain(l).endswith(":") or _LABEL.match(_plain(l))]
    for a, b in zip(marks, marks[1:] + [len(lines)]):
        seg = ([_label_content(lines[a])] if _LABEL.match(_plain(lines[a])) else []) + lines[a + 1:b]
        if any(_plain(l) for l in seg):
            lines = seg
            break
    paras = [[_plain(l) for l in p.split("\n") if _plain(l)] for p in re.split(r"\n\s*\n", "\n".join(lines))]
    paras = [p for p in paras if p]
    while len(paras) > 1 and (_CLOSING.match(paras[-1][0]) or _META.search(" ".join(paras[-1]))):
        paras = paras[:-1]
    if paras and all(_BULLET.match(l) for l in paras[0]):
        paras = [[_BULLET.sub("", paras[0][0])]]
    out = []
    for p in paras:
        par = _FIELD.sub("", "\n".join(p)).strip()
        m = _QUOTED.match(par)
        out.append(m.group(1).strip() if m and not re.search('["“”]', m.group(1)) else par)
    return "\n\n".join(par for par in out if par) or (text or "").strip()


# ------------------------------------------------------------------ data
def load_reviews(path, n=4000, seed=0):
    pool = pd.read_csv(path, usecols=["firm", "date_review", "overall_rating"] + ITEMS)
    pool["date_review"] = pd.to_datetime(pool["date_review"], errors="coerce")
    pool = pool[(pool.date_review >= "2019-01-01") & (pool.date_review < "2021-07-01")]
    for it in ITEMS:
        pool = pool[pool[it].fillna("").str.split().str.len().between(1, 300)]
    df = pool.groupby("firm", group_keys=False).apply(lambda g: g.sample(min(len(g), 20), random_state=seed))
    return df.sample(min(n, len(df)), random_state=seed).reset_index(drop=True)


def records(path):
    with gzip.open(path, "rt", encoding="utf-8") as fh:
        return [json.loads(l) for l in fh if l.strip()]


# ------------------------------------------------------------------ detector
def train(ai_texts, human_texts):
    vec = TfidfVectorizer(analyzer="char_wb", ngram_range=(2, 4), min_df=2, sublinear_tf=True)
    X = vec.fit_transform(list(ai_texts) + list(human_texts))
    y = np.r_[np.ones(len(ai_texts)), np.zeros(len(human_texts))]
    return vec, LogisticRegression(max_iter=2000, C=1.0, random_state=0).fit(X, y)


def score(model, texts):
    vec, clf = model
    return clf.predict_proba(vec.transform(list(texts)))[:, 1]


def score_by_fold(models, texts):
    """Score each new text with one fold detector, chosen by a hash of the text, so that survey scores follow
    the out-of-fold law of the development scores."""
    texts = ["" if t is None else str(t) for t in texts]
    pick = np.array([int(hashlib.sha1(t.encode()).hexdigest()[:8], 16) % len(models) for t in texts], int)
    out = np.empty(len(texts))
    for f, model in enumerate(models):
        if (pick == f).any():
            out[pick == f] = score(model, [t for t, k in zip(texts, pick) if k == f])
    return out


# ------------------------------------------------------------------ main
CSV, AI, OUT = HERE.parent / "data" / "glassdoor_reviews.csv", HERE.parent / "data" / "ai_answers", HERE / "populations"
OUT.mkdir(exist_ok=True)
df = load_reviews(CSV)
n, J = len(df), len(ITEMS)
dev = np.random.default_rng(0).uniform(size=n) < 0.3          # development employees
orig = df[ITEMS].fillna("").to_numpy(object)
orig_codes = np.column_stack([code_texts(orig[:, j]) for j in range(J)])
rating = df["overall_rating"].to_numpy(float)
x = np.digitize(np.where(np.isnan(rating), 3, rating), [2.5, 3.5])

# references by Claude and GPT for development employees (tag ref|employee|item|mode)
refs = [r for r in records(AI / "references.jsonl.gz") if r["model"] in REF_MODELS]
tags = [r["tag"].split("|") for r in refs]
ref_emp = np.array([int(t[1]) for t in tags])
ref_item = np.array([ITEMS.index(t[2]) for t in tags])
keep = dev[ref_emp]
ref_emp, ref_item = ref_emp[keep], ref_item[keep]
ref_texts = np.array([as_pasted(r["text"]) for r, k in zip(refs, keep) if k], object)

# five detectors, cross-fitted with folds by employee; out-of-fold scores of the development human answers
dev_idx = np.where(dev)[0]
hum_texts, hum_emp = np.asarray(list(orig[dev].ravel()), object), np.repeat(dev_idx, J)
ids = np.unique(np.r_[ref_emp, hum_emp])
fold = dict(zip(ids, np.random.default_rng(0).permutation(len(ids)) % 5))
fa, fh = np.array([fold[e] for e in ref_emp]), np.array([fold[e] for e in hum_emp])
models, s_hum = [], np.zeros(len(hum_texts))
for f in range(5):
    model = train(ref_texts[fa != f], hum_texts[fh != f])
    s_hum[fh == f] = score(model, hum_texts[fh == f])
    models.append(model)
s_hum = s_hum.reshape(-1, J)

# survey AI answers (tag employee|item|mode) and AI twins written from the ratings alone (tag twin|employee|item)
by = defaultdict(list)
for r in records(AI / "replacements.jsonl.gz"):
    t = r["tag"].split("|")
    if r["model"] in SURVEY_MODELS:
        by[(int(t[0]), t[1])].append((t[2], r["text"]))
twins = {(int(t[1]), t[2]): r["text"] for r in records(AI / "twins.jsonl.gz") for t in [r["tag"].split("|")]}
survey = np.where(~dev)[0]

# thresholds flag the chosen share of the human answers of half of the development employees
tune = np.random.default_rng(7).uniform(size=len(dev_idx)) < 0.5
pick = np.random.default_rng(11)
for j, item in enumerate(ITEMS):
    ai_txt = []
    for i in survey:
        cand = by.get((int(i), item), [])
        ai_txt.append(as_pasted(cand[pick.integers(len(cand))][1] if cand else twins[(int(i), item)]))
    f_ai, f_own, r1 = score_by_fold(models, ai_txt), score_by_fold(models, orig[survey, j]), code_texts(ai_txt)
    for fpr in (0.10, 0.15, 0.20):
        thr = float(np.quantile(s_hum[tune, j], 1 - fpr))
        path = OUT / f"pop_{item}_fpr{round(fpr * 100):02d}.npz"
        np.savez(path, x=x[survey], r0=orig_codes[survey, j], f0=(f_own >= thr).astype(int), r1=r1,
                 f1=(f_ai >= thr).astype(int))
        print(f"{path.name}: FPR {(f_own >= thr).mean():.3f}, TPR {(f_ai >= thr).mean():.3f}", flush=True)
