import json
import google.generativeai as genai
import re

# Load your Gemini API key (ensure you set it via environment variable or securely otherwise)
GOOGLE_API_KEY = "APIKEY"
genai.configure(api_key=GOOGLE_API_KEY)

def load_json_data(filename):
    """Generic loader for any JSON file."""
    try:
        with open(filename, "r") as f:
            return json.load(f)
    except FileNotFoundError:
        print(f"Error: File not found: {filename}")
        return []
    except json.JSONDecodeError:
        print(f"Error: Invalid JSON in {filename}")
        return []

def create_prompt(c_constructs, promela_data):
    """Creates a prompt to suggest Promela constructs for C code constructs."""
    prompt = """
You are a system that analyzes C code constructs and suggests appropriate Promela constructs for modeling them.

Here are the C code constructs to be analyzed:
"""
    for construct in c_constructs:
        prompt += f"\n- Construct Type: {construct['construct_type']}\n  Code: {construct['code']}\n"

    prompt += """

Here is the Promela grammar (rules with descriptions):
"""
    for rule_data in promela_data:
        description = rule_data.get('description', 'No description available')
        prompt += f"\n- Rule: {rule_data['rule']}\n  Description: {description}"

    prompt += """

Analyze each C code construct and suggest the most suitable Promela constructs (from the provided Promela grammar) to model its behavior.
Provide your answer in JSON format. For each C construct, return a JSON object with the following keys:
- "c_construct_type": the construct_type from the C code
- "c_code": the code snippet
- "suggested_promela_rules": list of most relevant Promela rules (as strings)
- "explanation": why those Promela rules are suitable

IMPORTANT: The output must be a valid JSON array only. Do not include any text, explanation, or comments outside of the JSON array.

Example Output:
[
  {
    "c_construct_type": "if statement",
    "c_code": "if (x > 0) { y = 1; }",
    "suggested_promela_rules": ["if :: (expr) -> sequence fi"],
    "explanation": "The Promela 'if' allows for conditional execution, like the C 'if'."
  },
  {
    "c_construct_type": "while loop",
    "c_code": "while (i < 10) { i++; }",
    "suggested_promela_rules": ["do :: (expr) -> sequence od"],
    "explanation": "Promela 'do' represents looping, similar to C's 'while'."
  }
]
"""
    return prompt

def get_llm_response(prompt, model_name="gemini-1.5-flash-latest"):
    """Gets a response from the LLM."""
    try:
        model = genai.GenerativeModel(model_name)
        response = model.generate_content(prompt)
        return response.parts[0].text if response.parts else None
    except Exception as e:
        print(f"Error querying LLM: {e}")
        return None

def clean_json_text(text):
    # Remove triple‑backtick fences
    text = re.sub(r"```(?:json)?", "", text)
    # Extract the first JSON array in the text
    m = re.search(r"\[\s*\{.*?\}\s*\]", text, re.DOTALL)
    return m.group(0) if m else text


def parse_llm_response(llm_response):
    try:
        return json.loads(llm_response)
    except json.JSONDecodeError:
        cleaned = clean_json_text(llm_response)
        return json.loads(cleaned)

def save_json_to_file(data, filename):
    """Save the parsed JSON data to a file."""
    try:
        with open(filename, 'w') as outfile:
            json.dump(data, outfile, indent=4)
        print(f"Parsed JSON saved to {filename}")
    except Exception as e:
        print(f"Error saving JSON to file: {e}")


def main():
    c_constructs = load_json_data("c_code_analysis.json")
    promela_data = load_json_data("promela_grammar_embeddings.json")

    if not c_constructs or not promela_data:
        print("Error: Could not load required data. Exiting.")
        return

    prompt = create_prompt(c_constructs, promela_data)
    llm_response = get_llm_response(prompt)

    parsed_response = parse_llm_response(llm_response)
    if parsed_response:
        save_json_to_file(parsed_response, "parsed_output.json")
    else:
        print("Error: Could not parse LLM response.")

if __name__ == "__main__":
    main()
