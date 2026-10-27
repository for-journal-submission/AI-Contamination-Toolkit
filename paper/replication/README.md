# Replication code for Table 2

```
python3 -m pip install -r requirements.txt
python3 download_data.py                 # Glassdoor reviews from Kaggle -> data/glassdoor_reviews.csv
cd table2
python3 build_populations.py             # about 35 s
python3 table2.py                        # about 30 s; prints the rows of Table 2
```

| Script | What it does |
|---|---|
| `download_data.py` | Downloads `glassdoor_reviews.csv` (293 MB) from Kaggle, `davidgauthier/glassdoor-job-reviews`, with kagglehub, and checks the AI answers in `data/ai_answers/`. Without Kaggle access, download the file by hand and run `python3 download_data.py --csv /path/to/glassdoor_reviews.csv`. |
| `table2/build_populations.py` | Draws 4,000 pre-AI reviews (2019 to mid-2021, at most 20 per firm), codes each answer into six themes with a frozen keyword rule, trains a cross-fitted character n-gram detector on the reference models' answers, and writes the potential-outcome populations `table2/populations/pop_<item>_fpr10/15/20.npz` (Appendix, test bed). |
| `table2/table2.py` | The Monte Carlo of Table 2 (Appendix, Monte Carlo study): no correction, deleting flagged answers, and the IV design with its delta-method interval; 1,000 surveys per cell, N = 3,000 and 6,000. |

## Data

- Glassdoor reviews: Kaggle, `davidgauthier/glassdoor-job-reviews` (version 11), downloaded by `download_data.py`.
- AI answers, generated through OpenRouter on October 1–3, 2026, shipped in `data/ai_answers/` (gzipped JSON lines with fields `tag`, `model`, `text`; no model is called):
  - `replacements.jsonl.gz`: answers written for survey employees by Gemini 3.8 Flash and DeepSeek V4.1 Flash;
  - `references.jsonl.gz`: answers by Claude Sonnet 5 and GPT that train the detector. GPT was called as `openai/gpt-chat-latest`, which on the generation dates pointed to the August 2026 chat version of GPT-5.6 Sol;
  - `twins.jsonl.gz`: answers by Claude Sonnet 5 and GPT written from an employee's ratings alone, used for employees without a Gemini or DeepSeek answer.

Tested with Python 3.13, numpy 2.5.3, pandas 3.0.5, scikit-learn 1.9.1, scipy 1.18.1. Other pandas or scikit-learn versions can change the sample or the detector slightly.
