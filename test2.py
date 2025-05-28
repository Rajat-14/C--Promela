import json
import google.generativeai as genai

# Load your Gemini API key
GOOGLE_API_KEY = "APIKEY"  # Replace with your actual Gemini API key
genai.configure(api_key=GOOGLE_API_KEY)


def load_json_data(filename="parsed_output.json"):
    """Loads the JSON data from the given file.  Handles potential errors."""
    try:
        with open(filename, "r") as f:
            data = json.load(f)
        return data
    except FileNotFoundError:
        print(f"Error: File not found: {filename}")
        return None
    except json.JSONDecodeError:
        print(f"Error: Invalid JSON in {filename}")
        return None
    except Exception as e:
        print(f"An unexpected error occurred: {e}")
        return None

def load_c_source(filename="my_code.c"):
    """Loads the original C source code for review."""
    try:
        with open(filename, "r") as f:
            return f.read()
    except FileNotFoundError:
        print(f"Warning: C source file not found: {filename}")
        return ""
    except Exception as e:
        print(f"Warning: Could not read C source file: {e}")
        return ""

def generate_promela_code(data):
    """Generates Promela code from the given data using the Gemini API."""
    prompt = """
    You are a system that translates C code constructs into Promela code for verification.
    You are given a JSON array where each element describes a C code construct and suggests Promela rules for modeling it.
    Your task is to generate a complete and runnable Promela program that accurately models the behavior of the provided C code.

    Here is the input JSON data:
    """
    prompt += json.dumps(data, indent=2)  # Include the data in the prompt

    # Load and include original C source for printf review
    c_code = load_c_source()
    if c_code:
        prompt += "\nAdditionally, here is the original C source code (my_code.c):\n" + c_code
        prompt += ("\nPlease review the conversion and ensure that all printf statements in the C source "
                   "are modeled or noted. If any printf calls are missing from the JSON constructs, identify them explicitly before providing the Promela code.")


    prompt += """

  Based on the provided C code constructs and the Promela grammar rules defined earlier, generate a complete and runnable Promela program.

Ensure that:
- All necessary `proctype`, `chan`, `typedef`, variables, and control-flow constructs are included.
- The output Promela code accurately reflects the behavior of the original C code, especially with regard to concurrency, function calls, and state transitions.

IMPORTANT:
- Do not include any explanation, description, or comments before or after the Promela code. The response should ONLY contain the Promela code.
- Please make sure that no variable remains undeclared
- All global declarations (the typedef node, node_mem array, and node_valid array) appear at the top of the file, before any proctype or init blocks.
- **Do not** wrap your entire Promela output in triple-backticks or any code fences.
- Follow the given Promela grammar strictly. Only use constructs explicitly defined in the grammar.
- Do not use `for` loops. Use `do` clauses (with guarded commands) only where appropriate.
- Use `do-od` loops only when the original C code contains a `while` or `do-while` loop.
- For `switch-case` constructs in C, use `if-fi` blocks with guarded clauses.
- Avoid constructs not defined in the grammar, such as inline comments or unstructured jumps unless defined (e.g., `goto`, `label`, etc.).
- Struct pointers should be modeled using integer indices and arrays.
- All function calls (including recursive ones) must be modeled using `chan` return mechanisms and `proctype`s, as shown in the examples.
- Every `main` function in C must be modeled as a `proctype` named `main` with a `chan in_main` parameter.
- Include an `init` block that:
    - Declares `chan ret_main = [0] of {int};`
    - Declares `int result;`
    - Runs the `main` proctype with `ret_main`
    - Receives the result with `ret_main ? result;`
- If you call a proctype, then write run before it.
- If a variable is assigned a value greater than or equal to 256, use `int` instead of `byte` when declaring that variable.
- Avoid writing else -> skip to exit the do clause instead use else -> break or left it blank the do clause will automatically be terminated
- Arrays must **not** be initialized at the time of declaration. Instead, they must be initialized element by element after declaration. For example:
    ✅ Valid:
        int nums[4];
        nums[0] = 121;
        nums[1] = 64;
        nums[2] = 0;
        nums[3] = -10;

    ❌ Invalid:
        int nums[4] = {121, 64, 0, -10};
- Any channel declaration inside proctype must be done first before the other code starts
- For malloc and free please refer the example 4
- Please declare the int result in the init block if used



Learn and generalize patterns from the examples provided below to handle similar constructs.

---
Examples:

C Input:
    switch (x)
    {
    case 0:
        a++;
        b++;
    case 1:
        a--;
        b--;
    default:
        break;
    }

Promela Output:
    if
    ::(x==0)->
      a++;
      b++;
    ::(x==1)->
      a--;
      b--;
    ::else ->
      skip;
    fi

C Input:
    struct node
    {
        struct node *next;
        int value;
    };
    struct node *tail;

    void test(struct node *tmp)
    {
        tail->next = tmp;
        tail = tmp;
    }

Promela Output:
    typedef node
    {
        int next;
        int value;
    }
    node node_mem[9];
    int node_valid[9];
    int tail;

    proctype test(chan in_test; int tmp)
    {
        node_mem[tail].next = tmp;
        tail = tmp;
        in_test ! 0;
        goto end;
    end:
        printf("End of test");
    }

C Input:
    int gcd(int x, int y){
        if(y == 0) return x;
        else return gcd(y, x % y);
    }

Promela Output:
    proctype gcd(chan in_gcd; int x; int y){
        chan ret_gcd = [0] of { int };
        int tmp;
        if
        :: (y == 0) ->
            in_gcd ! x;
            goto end;
        :: else ->
            run gcd(ret_gcd, y, (x % y));
            ret_gcd ? tmp;
            in_gcd ! tmp;
            goto end;
        fi;
    end:
        printf("End of gcd");
    }
C Input:
    struct node
    {
        struct node *next;
        int value;
    };

    void test()
    {
        struct node *new = malloc(sizeof(struct node));
        free(new);
    }

Promela Output:
    typedef node {
        int next;
        int value;
    }
    node node_mem[9];
    int node_valid[9];

    proctype test(chan in_test){
        int malloc_node_c;
        int new;
        int tmp;
        atomic {
            malloc_node_c = 1;
            do
            :: (malloc_node_ c >= 9) -> break
            :: else ->
                if 
                ::(node_valid[malloc_node_c] ==0)->
                    node_valid[malloc_node_c] = 1;
                    break
                :: else -> malloc_node_c ++
                fi;
            od;
            assert (malloc_node_c < 9);
            tmp = malloc_node_c
        };
        new = tmp;
        d_step {
            node_valid[new] = 0;
            node_mem[new].next = 0;
            node_mem[new].value = 0
        }
        in_test ! 0;
        goto end;
    end:
        printf ("End of test");
    }


"""


    try:
        model = genai.GenerativeModel("gemini-1.5-flash-latest")
        response = model.generate_content(prompt)
        return response.text
    except Exception as e:
        print(f"Error generating Promela code: {e}")
        return None



def save_promela_code(promela_code, filename="generated.pml"):
    """Saves the generated Promela code to a file.  Handles potential errors."""
    if not promela_code:
        print("Error: No Promela code to save.")
        return False

    try:
        with open(filename, "w") as f:
            f.write(promela_code)
        print(f"Promela code saved to {filename}")
        return True
    except Exception as e:
        print(f"Error saving Promela code: {e}")
        return False



def main():
    """Main function to orchestrate the process."""
    c_data = load_json_data()  # Load the JSON data
    if c_data is None:
        print("Exiting...")
        return  # Exit if loading failed

    promela_code = generate_promela_code(c_data)  # Generate Promela code
    if promela_code:
        save_result = save_promela_code(promela_code)  # Save the code
        if not save_result:
            print("Saving the promela code failed")
    else:
        print("Error: Failed to generate Promela code.")



if __name__ == "__main__":
    main()

