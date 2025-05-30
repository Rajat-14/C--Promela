# C to Promela Code Translator using LLM (Gemini API)

This project converts C code constructs into equivalent **Promela** syntax using Google's **Gemini LLM**. 
It's useful for translating C programs into models that can be verified with the SPIN model checker.

---

## Features

- Extracts C constructs (`if`, `while`, `malloc`, etc.)
- Uses Promela grammar + LLM for accurate translation
- Outputs Promela equivalents with explanations in JSON
- Handles `malloc`/`free` via simulated memory arrays

---

##  Project Structure

- `my_code.c` — Input C file  
- `extract_c_constructs.py` — Extracts constructs using regex  
- `test1.py` — (Main logic) Generates prompt + queries Gemini  
- `c_code_analysis.json` — C construct info  
- `promela_grammar_embeddings.json` — Promela rule descriptions  
- `parsed_output.json` — LLM's Promela suggestions  

---

## How It Works

1. Extract C code constructs → `c_code_analysis.json`
2. Load Promela grammar → `promela_grammar_embeddings.json`
3. Send prompt to Gemini LLM
4. Get Promela rules + explanations in JSON
5. Save output to `parsed_output.json`

---

## 🧾 Why JSON?

JSON is used for its:
- Human-readable structure
- Easy integration with code
- Example:
```json
{
  "c_construct_type": "if",
  "c_code": "if (x > 0) { y = 1; }",
  "suggested_promela_rules": ["if :: (expr) -> sequence fi"],
  "explanation": "Promela 'if' models C's conditional logic."
}
