"""Put the Glassdoor reviews (Kaggle davidgauthier/glassdoor-job-reviews, version 11) at data/glassdoor_reviews.csv,
check the file against its SHA-256, and check that the shipped AI answers are in data/ai_answers/.

    python3 download_data.py                 # download with kagglehub
    python3 download_data.py --csv FILE      # use a copy of glassdoor_reviews.csv downloaded by hand
"""
import argparse
import hashlib
import shutil
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA = HERE / "data"
CSV = DATA / "glassdoor_reviews.csv"
VERSION = "davidgauthier/glassdoor-job-reviews/versions/11"
SHA256 = "9273f0ba1a4643ccd4fbd47ac2aa016b6d46c2c3444dc3f0039d6f1d20644387"
AI_FILES = ["references.jsonl.gz", "replacements.jsonl.gz", "twins.jsonl.gz"]

ap = argparse.ArgumentParser()
ap.add_argument("--csv", help="local copy of glassdoor_reviews.csv (skips the download)")
args = ap.parse_args()

if args.csv:
    src = Path(args.csv)
else:
    try:
        import kagglehub
        src = Path(kagglehub.dataset_download(VERSION)) / "glassdoor_reviews.csv"
    except Exception as err:
        sys.exit(f"kagglehub download failed ({err}).\nDownload glassdoor_reviews.csv by hand from "
                 "https://www.kaggle.com/datasets/davidgauthier/glassdoor-job-reviews (version 11) and run\n"
                 "    python3 download_data.py --csv /path/to/glassdoor_reviews.csv")
DATA.mkdir(exist_ok=True)
if src.resolve() != CSV.resolve():
    shutil.copyfile(src, CSV)
print(f"reviews: {CSV} ({CSV.stat().st_size / 1e6:.0f} MB)")
h = hashlib.sha256()
with open(CSV, "rb") as f:
    for block in iter(lambda: f.read(1 << 20), b""):
        h.update(block)
if h.hexdigest() == SHA256:
    print("SHA-256 matches version 11")
else:
    print(f"warning: SHA-256 {h.hexdigest()} differs from version 11 ({SHA256}); Table 2 may not reproduce")

missing = [f for f in AI_FILES if not (DATA / "ai_answers" / f).exists()]
if missing:
    sys.exit(f"missing AI answers in data/ai_answers/: {missing}")
print("AI answers: " + ", ".join(AI_FILES) + " present")
