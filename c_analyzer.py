import re
import json
import google.generativeai as genai


GOOGLE_API_KEY = "APIKEY"  
genai.configure(api_key=GOOGLE_API_KEY)
model = genai.GenerativeModel('gemini-1.5-flash-latest')


def extract_if_statements(c_code):
    constructs = []
    i = 0
    length = len(c_code)

    while i < length:
        # Look for an "if" statement
        match = re.search(r'\bif\s*\(', c_code[i:])
        if not match:
            break
        start = i + match.start()
        i = start

        # Now find the full "if-else" block
        brace_stack = []
        end = i

        while end < length:
            if c_code[end] == '{':
                brace_stack.append('{')
            elif c_code[end] == '}':
                if brace_stack:
                    brace_stack.pop()
                # When we've closed the main block
                if not brace_stack:
                    end += 1
                    # Check for else or else-if
                    while True:
                        remainder = c_code[end:].lstrip()
                        if remainder.startswith("else"):
                            skip = len(c_code[end:]) - len(remainder)
                            end += skip + len("else")

                            if remainder[len("else"):].lstrip().startswith("if"):
                                end += len(remainder[len("else"):]) - len(remainder[len("else"):].lstrip())
                                # Skip "if (...)"
                                paren_count = 0
                                while end < length:
                                    if c_code[end] == '(':
                                        paren_count += 1
                                    elif c_code[end] == ')':
                                        paren_count -= 1
                                        if paren_count == 0:
                                            end += 1
                                            break
                                    end += 1
                            # Now handle block
                            while end < length and c_code[end] != '{':
                                end += 1
                            if end < length and c_code[end] == '{':
                                brace_stack.append('{')
                                end += 1
                                while end < length and brace_stack:
                                    if c_code[end] == '{':
                                        brace_stack.append('{')
                                    elif c_code[end] == '}':
                                        brace_stack.pop()
                                    end += 1
                        else:
                            break
                    break
            end += 1

        if_code = c_code[start:end]
        constructs.append({"type": "if_statement", "code": if_code.strip()})
        i = end

    return constructs

def extract_c_constructs(c_code):
    """
    Extracts C code constructs from the given C code.

    Args:
        c_code (str): The C code to analyze.

    Returns:
        list: A list of dictionaries, where each dictionary represents a C construct
              and contains the 'type' and 'code' of the construct.
    """
    constructs = []

    # Function definitions
    function_matches = re.findall(
        r"(?:static\s+)?(?:inline\s+)?[a-zA-Z_][\w]*\s+\**\s*[a-zA-Z_][\w]*\s*\([^)]*\)\s*\{[^}]*\}",
        c_code,
        re.DOTALL
    )
    for match in function_matches:
        constructs.append({"type": "function_definition", "code": match.strip()})

    # Variable declarations (global and local), excluding return statements
    variable_matches = re.findall(
        r"(?:static\s+)?(?:const\s+)?[a-zA-Z_][\w]*\s+\**\s*[a-zA-Z_][\w]*\s*(?:\[[^\]]*\])?\s*(?:=\s*[^;]+)?;",
        c_code
    )
    for match in variable_matches:
        code = match.strip()
        # Skip return statements that accidentally match
        if code.startswith('return '):
            continue
        constructs.append({"type": "variable_declaration", "code": code})
    

    # Return statements
    return_matches = re.findall(r"return\s+[^;]+;", c_code)
    for match in return_matches:
        constructs.append({"type": "return_statement", "code": match.strip()})

    # For loops
    for_loop_matches = re.findall(r"for\s*\([^)]*\)\s*\{[^}]*\}", c_code, re.DOTALL)
    for match in for_loop_matches:
        constructs.append({"type": "for_loop", "code": match.strip()})

    # While loops
    while_loop_matches = re.findall(r"while\s*\([^)]*\)\s*\{[^}]*\}", c_code, re.DOTALL)
    for match in while_loop_matches:
        constructs.append({"type": "while_loop", "code": match.strip()})

    # If statements (including else if and else)
    if_statement_matches = re.findall(
        r"if\s*\([^)]*\)\s*\{[^}]*\}(?:\s*else\s+if\s*\([^)]*\)\s*\{[^}]*\})*(?:\s*else\s*\{[^}]*\})?",
        c_code,
        re.DOTALL
    )
    constructs.extend(extract_if_statements(c_code))

    
      # Struct definitions
    struct_matches = re.findall(
        r"struct\s+[a-zA-Z_][\w]*\s*\{[^}]*\}\s*;",
        c_code,
        re.DOTALL
    )
    for match in struct_matches:
        constructs.append({"type": "struct_definition", "code": match.strip()})

     # Ternary operators (simple assignment-based detection)
    ternary_matches = re.findall(
        r"[a-zA-Z_][\w]*\s*=\s*[^;?]+?\?[^:;]+:[^;]+;",
        c_code
    )
    for match in ternary_matches:
        constructs.append({"type": "ternary_operator", "code": match.strip()})
    
    # Switch-case statements
    switch_matches = re.findall(
        r"switch\s*\([^)]*\)\s*\{(?:[^{}]*\{[^}]*\}[^{}]*)*[^}]*\}",
        c_code,
        re.DOTALL
    )
    for match in switch_matches:
        constructs.append({"type": "switch_case", "code": match.strip()})
    
    

    return constructs


# Query the LLM for explanations
def query_llm(construct):
    """
    Queries the LLM to get an explanation of the given C code construct.

    Args:
        construct (dict): A dictionary representing the C code construct,
                          containing 'type' and 'code'.

    Returns:
        str: The LLM's explanation of the C code construct, or an error message.
    """
    prompt = f"""
    Explain the following C code construct. Provide a concise explanation of its purpose and functionality.

    C code:
    ```c
    {construct['code']}
    ```
    """
    try:
        response = model.generate_content(prompt)
        # Extract the text from the response
        if response.parts:
            explanation = response.parts[0].text.strip()
        else:
            explanation = response.text.strip()

        return explanation
    except Exception as e:
        return f"Error querying LLM: {e}"



def main():
    """
    Reads C code from a file, extracts C constructs, queries the LLM for
    explanations, and saves the results to a JSON file.
    """
    c_file_path = "my_code.c"  # Replace with the path to your C file
    try:
        with open(c_file_path, 'r') as file:
            c_code = file.read()
    except FileNotFoundError:
        print(f"Error: File not found at {c_file_path}")
        return

    # Extract constructs
    constructs = extract_c_constructs(c_code)
    results = []

    # Query LLM for each construct
    for construct in constructs:
        explanation = query_llm(construct)
        results.append({
            "construct_type": construct["type"],
            "code": construct["code"],
            "explanation": explanation
        })

    # Save to JSON
    output_file = "c_code_analysis.json"
    try:
        with open(output_file, 'w') as json_file:
            json.dump(results, json_file, indent=4)
        print(f"Analysis saved to {output_file}")
    except Exception as e:
        print(f"Error saving analysis to file: {e}")



if __name__ == "__main__":
    main()
