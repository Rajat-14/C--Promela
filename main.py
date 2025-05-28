from sentence_transformers import SentenceTransformer
import json

promela_rules = [
    "<spec> ::= { <declaration> | <typedef> | <proctype> | <init> | <never> | <inline> }",

    
    "<typedef> ::= 'typedef' 'struct' [ <identifier> ] '{' <declaration-list> '}' <identifier> ';'",

    
    "<declaration> ::= <type> <pointer-ident-list> [ '[' <integer> ']' ] ';'",

    "<declaration-list> ::= { <type> <pointer-ident-list> ';' }",

    "<type> ::= 'bool' | 'bit' [ '[' <range> ']' ] | 'short' [ '[' <range> ']' ] | "
              "'int' [ '[' <range> ']' ] | 'mtype' [ '=' '{' <ident-list> '}' ] | "
              "'chan' [ '[' <range> ']' ] [ '[' <range> ']' ] | <identifier>",

    "<pointer-ident-list> ::= <pointer-ident> { ',' <pointer-ident> }",
    "<pointer-ident> ::= [ '*' ] <identifier>",

    "<range> ::= <integer> [ ':' <integer> ]",
    "<ident-list> ::= <identifier> { ',' <identifier> }",

   
    "<proctype> ::= 'proctype' <identifier> '(' [ <param-list> ] ')' '{' <stmt-list> '}'",
    "<param-list> ::= <param> { ',' <param> }",
    "<param> ::= [ 'chan' ] <identifier> [ '[' <range> ']' ]",

    "<init> ::= 'init' '{' <stmt-list> '}'",
    "<never> ::= 'never' '{' <stmt-list> '}'",
    "<inline> ::= 'inline' <identifier> '(' [ <param-list> ] ')' '{' <stmt-list> '}'",

    "<stmt-list> ::= { <statement> }",

 
    "<statement> ::= <assignment> ';' | <send> ';' | <recv> ';' | <printf> ';' | "
                    "<assert> ';' | <if-stmt> | <do-stmt> | "
                    "'atomic' '{' <stmt-list> '}' | 'd_step' '{' <stmt-list> '}' | "
                    "'break' ';' | <label> ':' | 'goto' <identifier> ';' | 'skip' ';' | "
    "<function-call> ';'",

    # ——— Function calls (malloc(), free(), any call) ———
    "<function-call> ::= <identifier> '(' [ <expr-list> ] ')'" ,
    "<expr-list> ::= <expr> { ',' <expr> }",

    "<assignment> ::= <lhs> '=' <expr>",
    "<lhs> ::= <identifier> [ '[' <expr> ']' ] | '*' <identifier> | "
              "<identifier> '.' <identifier> | <identifier> '->' <identifier>",

    "<expr> ::= <expr> <binary-op> <expr> | <unary-op> <expr> | <primary>",

    "<binary-op> ::= '+' | '-' | '*' | '/' | '%' | '==' | '!=' | '<' | '<=' | '>' | '>=' | "
                    "'&&' | '||' | '&' | '|' | '^' | '<<' | '>>'",

    "<unary-op> ::= '!' | '~' | '-' | 'sizeof' | '&' | '*'",

    "<primary> ::= <integer> | <identifier> [ '[' <expr> ']' ] | '(' <expr> ')' | "
                  "'true' | 'false' | <identifier> '.' <identifier> | <identifier> '->' <identifier>",

    "<if-stmt> ::= 'if' <if-clause-list> [ <else-clause> ] 'fi'",
    "<if-clause-list> ::= { '::' <guard> '->' <stmt-list> }",
    "<else-clause> ::= '::' 'else' '->' <stmt-list>",

    "<do-stmt> ::= 'do' <do-clause-list> [ <else-clause> ] 'od'",
    "<do-clause-list> ::= { '::' <guard> '->' <stmt-list> }",

    "<guard> ::= <expr> | <recv>",

    "<send> ::= <chan-id> '!' [ <expr> { ',' <expr> } ]",
    "<recv> ::= <chan-id> '?' [ '[' <guard> ']' ] <lhs> { ',' <lhs> }",

    "<label> ::= <identifier>",
    "<assert> ::= 'assert' '(' <expr> ')'",
    "<printf> ::= 'printf' '(' <string> { ',' <expr> } ')'",

    "Comments: // … (single-line), /* … */ (multi-line)"
]




# Load the Sentence Transformer model
model = SentenceTransformer('all-MiniLM-L6-v2')

# Generate embeddings for the grammar rules
grammar_embeddings = model.encode(promela_rules)

# Create a list of dictionaries, where each dictionary contains a rule and its corresponding embedding
rule_embeddings_data = []
for i, rule in enumerate(promela_rules):
    rule_embeddings_data.append({
        "rule": rule,
        "embedding": grammar_embeddings[i].tolist()  # Convert the NumPy array to a list
    })

# Save the data to a JSON file
output_file_path = "promela_grammar_embeddings.json"
with open(output_file_path, "w") as f:
    json.dump(rule_embeddings_data, f, indent=4)  # Use indent=4 for pretty formatting

print(f"Embeddings saved to {output_file_path}")
