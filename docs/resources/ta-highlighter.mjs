/**
 * MyST plugin to add ByMC / .ta format syntax highlighting support.
 *
 * This plugin transforms code blocks with lang="ta" or "c" (for ByMC files)
 * to add inline span nodes with styles for syntax highlighting.
 *
 * This code has been generated with the help of AI.
 */

// ByMC skeleton keywords (top-level structure)
const TA_SKELETON_KEYWORDS = new Set([
  "thresholdAutomaton",
  "threshAuto",
  "TA",
  "ta",
  "skel",
]);

// ByMC block keywords
const TA_BLOCK_KEYWORDS = new Set([
  "local",
  "shared",
  "parameters",
  "assumptions",
  "assume",
  "locations",
  "inits",
  "rules",
  "specifications",
  "spec",
  "define",
]);

// ByMC rule keywords
const TA_RULE_KEYWORDS = new Set(["when", "do", "unchanged", "reset"]);

// Boolean/LTL keywords
const TA_BUILTINS = new Set(["true", "false"]);

// Operators
const TA_OPERATORS = new Set([
  "->",
  ":=",
  "==",
  "!=",
  "<=",
  ">=",
  "<",
  ">",
  "&&",
  "||",
  "!",
  "<>",
  "[]",
  "+",
  "-",
  "*",
  "/",
]);

/**
 * Tokenize ByMC .ta code into an array of {type, value} tokens.
 */
function tokenizeTA(code) {
  const tokens = [];
  let i = 0;

  while (i < code.length) {
    const ch = code[i];

    // Block comments: /* ... */
    if (code.slice(i, i + 2) === "/*") {
      let comment = "/*";
      i += 2;
      while (i < code.length && code.slice(i, i + 2) !== "*/") {
        comment += code[i++];
      }
      if (i < code.length) {
        comment += "*/";
        i += 2;
      }
      tokens.push({ type: "comment", value: comment });
      continue;
    }

    // Line comments: // ...
    if (code.slice(i, i + 2) === "//") {
      let comment = "";
      while (i < code.length && code[i] !== "\n") {
        comment += code[i++];
      }
      tokens.push({ type: "comment", value: comment });
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

      if (TA_SKELETON_KEYWORDS.has(ident)) {
        tokens.push({ type: "keyword", value: ident });
      } else if (TA_BLOCK_KEYWORDS.has(ident)) {
        tokens.push({ type: "block", value: ident });
      } else if (TA_RULE_KEYWORDS.has(ident)) {
        tokens.push({ type: "rule", value: ident });
      } else if (TA_BUILTINS.has(ident)) {
        tokens.push({ type: "builtin", value: ident });
      } else {
        tokens.push({ type: "text", value: ident });
      }
      continue;
    }

    // Multi-character operators (check longest first)
    let matched = false;
    const sortedOps = Array.from(TA_OPERATORS).sort(
      (a, b) => b.length - a.length
    );
    for (const op of sortedOps) {
      if (code.slice(i, i + op.length) === op) {
        tokens.push({ type: "operator", value: op });
        i += op.length;
        matched = true;
        break;
      }
    }
    if (matched) continue;

    // Single character (punctuation like {, }, (, ), ;, :, etc.)
    tokens.push({ type: "text", value: ch });
    i++;
  }

  return tokens;
}

// Map token types to CSS class names
const classMap = {
  keyword: "ta-keyword",
  block: "ta-block",
  rule: "ta-rule",
  builtin: "ta-builtin",
  comment: "ta-comment",
  string: "ta-string",
  number: "ta-number",
  operator: "ta-operator",
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
  return { type: "text", value: token.value };
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

    const lineNumNode = {
      type: "span",
      class: "ta-line-number",
      children: [{ type: "text", value: String(lineNum) }],
    };

    const lineContentNode = {
      type: "span",
      class: "ta-line-content",
      children: lineTokens.map(tokenToNode),
    };

    lineNodes.push({
      type: "div",
      class: "ta-line",
      children: [lineNumNode, lineContentNode],
    });
  }

  return lineNodes;
}

/**
 * Transform to convert ```ta or ```c code blocks to styled div with spans
 */
const taTransform = {
  name: "ta-highlight-transform",
  doc: 'Transforms code blocks with lang="ta" or "c" to add ByMC syntax highlighting via styled spans',
  stage: "document",
  plugin: (_, utils) => (tree) => {
    utils.selectAll("code", tree).forEach((codeNode) => {
      // Match 'ta', 'bymc', or 'c' language (c is commonly used for .ta files)
      if (
        codeNode.lang === "ta" ||
        codeNode.lang === "bymc" ||
        codeNode.lang === "eta"
      ) {
        const code = codeNode.value || "";
        const tokens = tokenizeTA(code);

        const showLineNumbers = codeNode.showLineNumbers === true;

        codeNode.type = "div";

        if (showLineNumbers) {
          codeNode.class = "ta-code-block ta-with-line-numbers";
          codeNode.children = buildWithLineNumbers(tokens);
        } else {
          codeNode.class = "ta-code-block";
          codeNode.children = tokensToNodes(tokens);
        }

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
  name: "ByMC/TA Syntax Highlighter",
  transforms: [taTransform],
};

export default plugin;
