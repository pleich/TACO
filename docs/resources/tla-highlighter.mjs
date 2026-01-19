/**
 * MyST plugin to add TLA+ syntax highlighting support.
 *
 * This plugin transforms code blocks with lang="tla" to add
 * inline span nodes with styles for syntax highlighting.
 *
 * This code has been generated with the help of AI.
 */

// TLA+ keywords
const TLA_KEYWORDS = new Set([
  "MODULE",
  "EXTENDS",
  "CONSTANT",
  "CONSTANTS",
  "VARIABLE",
  "VARIABLES",
  "ASSUME",
  "ASSUMPTION",
  "AXIOM",
  "THEOREM",
  "LEMMA",
  "PROPOSITION",
  "COROLLARY",
  "PROOF",
  "PROVE",
  "BY",
  "DEF",
  "DEFS",
  "ONLY",
  "QED",
  "OBVIOUS",
  "OMITTED",
  "HAVE",
  "TAKE",
  "WITNESS",
  "PICK",
  "SUFFICES",
  "CASE",
  "NEW",
  "STATE",
  "ACTION",
  "TEMPORAL",
  "LOCAL",
  "INSTANCE",
  "WITH",
  "LET",
  "IN",
  "IF",
  "THEN",
  "ELSE",
  "CHOOSE",
  "EXCEPT",
  "DOMAIN",
  "SUBSET",
  "UNION",
  "ENABLED",
  "UNCHANGED",
  "SPECIFICATION",
  "INVARIANT",
  "PROPERTIES",
  "PROPERTY",
]);

// TLA+ built-in constants/types
const TLA_BUILTINS = new Set([
  "TRUE",
  "FALSE",
  "BOOLEAN",
  "STRING",
  "Nat",
  "Int",
  "Real",
  "Cardinality",
  "Processes",
  "TypeOk",
  "Init",
  "Next",
  "Spec",
]);

const TLA_CUSTOM_RESERVED = new Set(["NbOfCorrProc", "ProcessesLocations"]);

const TLA_OPERATORS = new Set([
  "/\\",
  "\\/",
  "~~>",
  "|->",
  "==",
  "=>",
  "->",
  "[]",
  "<>",
  "\\in",
  "\\E",
  "<<",
  ">>",
  "=",
]);

const TLA_INT_OPERATORS = new Set([
  "/=",
  "<",
  ">",
  ">=",
  "<=",
  "+",
  "-",
  "*",
  "/",
]);

/**
 * Tokenize TLA+ code into an array of {type, value} tokens.
 */
function tokenizeTLA(code) {
  const tokens = [];
  let i = 0;

  while (i < code.length) {
    const ch = code[i];

    // Block comments: (* ... *)
    if (code.slice(i, i + 2) === "(*") {
      let comment = "(*";
      i += 2;
      while (i < code.length && code.slice(i, i + 2) !== "*)") {
        comment += code[i++];
      }
      if (i < code.length) {
        comment += "*)";
        i += 2;
      }
      tokens.push({ type: "comment", value: comment });
      continue;
    }

    // Line comments: either ----, ====== or \*
    if (
      code.slice(i, i + 2) === "\\*" ||
      (ch === "-" && code.slice(i, i + 4) === "----") ||
      (ch === "=" && code.slice(i, i + 4) === "====")
    ) {
      let delim = "";
      while (i < code.length && !(code[i] === "\n")) {
        delim += code[i++];
      }
      tokens.push({ type: "comment", value: delim });
      continue;
    }

    // Strings: "..."
    if (ch === '"') {
      let str = '"';
      i++;
      while (i < code.length && code[i] !== '"') {
        if (code[i] === "\\" && i + 1 < code.length) {
          str += code[i++] + code[i++];
        } else {
          str += code[i++];
        }
      }
      if (i < code.length) {
        str += '"';
        i++;
      }
      tokens.push({ type: "string", value: str });
      continue;
    }

    // Numbers
    if (/[0-9]/.test(ch)) {
      let num = "";
      while (i < code.length && /[0-9]/.test(code[i])) {
        num += code[i++];
      }
      tokens.push({ type: "number", value: num });
      continue;
    }

    // Identifiers and keywords
    if (/[A-Za-z_]/.test(ch)) {
      let ident = "";
      while (i < code.length && /[A-Za-z0-9_]/.test(code[i])) {
        ident += code[i++];
      }

      if (TLA_KEYWORDS.has(ident)) {
        tokens.push({ type: "keyword", value: ident });
      } else if (TLA_BUILTINS.has(ident)) {
        tokens.push({ type: "builtin", value: ident });
      } else if (TLA_CUSTOM_RESERVED.has(ident)) {
        tokens.push({ type: "custom_reserved", value: ident });
      } else {
        tokens.push({ type: "text", value: ident });
      }
      continue;
    }

    // Multi-character operators (check longest first)
    let matched = false;
    const sortedOps = Array.from(TLA_OPERATORS)
      .concat(Array.from(TLA_INT_OPERATORS))
      .sort((a, b) => b.length - a.length);
    for (const op of sortedOps) {
      if (code.slice(i, i + op.length) === op) {
        if (TLA_OPERATORS.has(op)) {
          tokens.push({ type: "operator", value: op });
        } else {
          tokens.push({ type: "int_operator", value: op });
        }

        i += op.length;
        matched = true;
        break;
      }
    }
    if (matched) continue;

    // Single character
    tokens.push({ type: "text", value: ch });
    i++;
  }

  return tokens;
}

// Map token types to CSS class names
const classMap = {
  keyword: "tla-keyword",
  builtin: "tla-builtin",
  comment: "tla-comment",
  string: "tla-string",
  number: "tla-number",
  operator: "tla-operator",
  int_operator: "tla-int-operator",
  custom_reserved: "tla-custom",
};

/**
 * Convert a single token to a MyST node.
 */
function tokenToNode(token) {
  if (token.type === "text") {
    return { type: "text", value: token.value };
  }
  const className = classMap[token.type];
  if (className) {
    return {
      type: "span",
      class: className,
      children: [{ type: "text", value: token.value }],
    };
  }

  throw Error("Unknown token class");
}

/**
 * Convert tokens to an array of MyST nodes (text or span with class).
 */
function tokensToNodes(tokens) {
  return tokens.map(tokenToNode);
}

/**
 * Split tokens into lines, preserving token types across line breaks.
 */
function tokensToLines(tokens) {
  const lines = [[]];

  for (const token of tokens) {
    const parts = token.value.split("\n");

    for (let i = 0; i < parts.length; i++) {
      if (i > 0) {
        // Start a new line
        lines.push([]);
      }
      if (parts[i].length > 0) {
        lines[lines.length - 1].push({ type: token.type, value: parts[i] });
      }
    }
  }

  return lines;
}

/**
 * Build the code block with line numbers.
 */
function buildWithLineNumbers(tokens) {
  const lines = tokensToLines(tokens);
  const lineNodes = [];

  for (let i = 0; i < lines.length; i++) {
    const lineNum = i + 1;
    const lineTokens = lines[i];

    // Line number span
    const lineNumNode = {
      type: "span",
      class: "tla-line-number",
      children: [{ type: "text", value: String(lineNum) }],
    };

    // Line content span
    const lineContentNode = {
      type: "span",
      class: "tla-line-content",
      children: lineTokens.map(tokenToNode),
    };

    // Wrap in a line div
    lineNodes.push({
      type: "div",
      class: "tla-line",
      children: [lineNumNode, lineContentNode],
    });
  }

  return lineNodes;
}

/**
 * Transform to convert ```tla code blocks to styled div with spans
 */
const tlaTransform = {
  name: "tla-highlight-transform",
  doc: 'Transforms code blocks with lang="tla" to add syntax highlighting via styled spans',
  stage: "document",
  plugin: (_, utils) => (tree) => {
    utils.selectAll("code", tree).forEach((codeNode) => {
      if (codeNode.lang === "tla" || codeNode.lang === "tlaplus") {
        const code = codeNode.value || "";
        const tokens = tokenizeTLA(code);

        // Check if line numbers are requested
        const showLineNumbers = codeNode.showLineNumbers === true;

        // Convert to a div containing styled spans with CSS class
        codeNode.type = "div";

        if (showLineNumbers) {
          codeNode.class = "tla-code-block tla-with-line-numbers";
          codeNode.children = buildWithLineNumbers(tokens);
        } else {
          codeNode.class = "tla-code-block";
          codeNode.children = tokensToNodes(tokens);
        }

        // Clean up code-specific properties
        delete codeNode.value;
        delete codeNode.lang;
        delete codeNode.showLineNumbers;
      }
    });
  },
};

/**
 * MyST plugin definition.
 */
const plugin = {
  name: "TLA+ Syntax Highlighter",
  transforms: [tlaTransform],
};

export default plugin;
