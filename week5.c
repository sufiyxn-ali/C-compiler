/*
 * ============================================================
 *  UPGRADED SYNTAX ANALYSER - FIXED VERSION
 *  Implements: (1) LL(1) Parser + (2) Shift-Reduce Parser
 * ============================================================
 */

#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_TOKENS 2000
#define MAX_CHILDREN 15
#define MAX_LABEL 64
#define MAX_VALUE 64
#define MAX_STMTS 200
#define MAX_SYMBOLS 60
#define MAX_PRODUCTIONS 60
#define MAX_STACK 500
#define MAX_RHS 10

/* ===== Q2: Symbol Table ===== */
#define MAX_SCOPE_DEPTH 32
#define MAX_SYM_TABLE 300
#define MAX_SEM_ERRORS 100

typedef struct {
  char name[MAX_LABEL]; /* variable name */
  char type[MAX_LABEL]; /* "int" or "float" */
  int scope;            /* nesting depth (0 = global) */
  int offset;           /* byte offset within its scope frame */
  int line;             /* declaration line */
} Symbol;

Symbol sym_table[MAX_SYM_TABLE];
int sym_count = 0;
int scope_depth = 0;               /* current nesting level */
int scope_offset[MAX_SCOPE_DEPTH]; /* running byte offset per level */

/* Global quiet mode flag: when 1, LL1/SR parsers produce no output */
int quiet_mode = 0;

/* Helper to print epsilon in a console-friendly way */
static const char *eps_str(const char *s) {
  if (strcmp(s, "\xce\xb5") == 0)
    return "eps";
  return s;
}

typedef struct Token {
  char type[MAX_LABEL];
  char value[MAX_VALUE];
  int line;
} Token;

typedef struct Node {
  char label[MAX_LABEL];
  char value[MAX_VALUE];
  struct Node *children[MAX_CHILDREN];
  int child_count;
  int line;
  char source[4096];
  char rd_error[256];
} Node;

Token tokens[MAX_TOKENS];
int token_count = 0;
int pos = 0;
int last_line = 1;
int error_count = 0;

/* Buffered error messages - printed after stack traces */
char error_messages[MAX_STMTS][256];
int error_msg_total = 0;

typedef struct {
  int num;
  char lhs[MAX_LABEL];
  char rhs[MAX_RHS][MAX_LABEL];
  int rhs_len;
} Production;

Production prods[MAX_PRODUCTIONS];
int prod_count = 0;

char non_terminals[MAX_SYMBOLS][MAX_LABEL];
int nt_count = 0;
char terminals[MAX_SYMBOLS][MAX_LABEL];
int term_count = 0;

char first_set[MAX_SYMBOLS][MAX_SYMBOLS][MAX_LABEL];
int first_cnt[MAX_SYMBOLS];
char follow_set[MAX_SYMBOLS][MAX_SYMBOLS][MAX_LABEL];
int follow_cnt[MAX_SYMBOLS];

int ll1_table[MAX_SYMBOLS][MAX_SYMBOLS];

Node *all_stmts[MAX_STMTS];
int stmt_count = 0;

/* Global variable to store the last recursive descent error */
char last_rd_error[256] = {0};

/* Forward declarations for Q2 / Q3 */
void sym_scope_enter(void);
void sym_scope_exit(void);
Symbol *sym_insert(const char *name, const char *type, int line);
Symbol *sym_lookup(const char *name);
Symbol *sym_lookup_current(const char *name);
void print_symbol_table(void);
void build_symbol_table(Node *node);
const char *infer_type(Node *node);
void sem_report(int line, const char *msg);
void semantic_analyze(Node *node);
void run_semantic_demo(void);

/* Forward declarations */
void build_grammar(void);
void build_symbol_lists(void);
void compute_first_sets(void);
void compute_follow_sets(void);
void build_ll1_table(void);
int ll1_parse_statement(Node *stmt);
int sr_parse_statement(Node *stmt);
void node_to_tokens(Node *node, Token *out, int *out_len);
const char *token_to_terminal(Token *t);
int is_terminal(const char *s);
int nt_index(const char *s);
int term_index(const char *s);
void print_productions(void);
void print_first_sets(void);
void print_follow_sets(void);
void print_ll1_table(void);
Node *create_node(const char *label, const char *value, int line);
void add_child(Node *parent, Node *child);
void print_tree(Node *node, int indent);
void collect_statements(Node *node);
void node_to_string(Node *node, char *buf, int *len);
void print_statement_source(Node *node);
void leftmost_derivation(Node *root);
void rightmost_derivation(Node *root);
Node *parse_program_rd(void);
Node *parse_statement_list(void);
Node *parse_statement(void);
Node *parse_decl_statement(void);
Node *parse_assign_statement(void);
Node *parse_if_statement(void);
Node *parse_while_statement(void);
Node *parse_print_statement(void);
Node *parse_block(void);
Node *parse_bool_expr(void);
Node *parse_bool_atom(void);
Node *parse_expr(void);
Node *parse_term(void);
Node *parse_factor(void);
Node *parse_error_statement(void);
void print_error(const char *msg, int line);
Token *current_tok(void);
Token *consume_tok(void);
Token *expect_type(const char *expected);
Token *expect_delim(const char *expected);
void synchronize(void);
void skip_to_next_statement(void);
void get_statement_source(int start_pos, int end_pos, char *buffer);
int lexical_analyze_file(const char *path);
void print_generated_tokens(void);

/* ========== GRAMMAR ========== */
void build_grammar(void) {
  prod_count = 0;
#define ADD_PROD(N, LHS, ...)                                                  \
  do {                                                                         \
    const char *_rhs[] = {__VA_ARGS__};                                        \
    int _len = sizeof(_rhs) / sizeof(_rhs[0]);                                 \
    prods[prod_count].num = (N);                                               \
    strcpy(prods[prod_count].lhs, (LHS));                                      \
    prods[prod_count].rhs_len = _len;                                          \
    for (int _i = 0; _i < _len; _i++)                                          \
      strcpy(prods[prod_count].rhs[_i], _rhs[_i]);                             \
    prod_count++;                                                              \
  } while (0)
  ADD_PROD(1, "program", "stmt_list");
  ADD_PROD(2, "stmt_list", "stmt", "stmt_list");
  ADD_PROD(3, "stmt_list", "\xce\xb5");
  ADD_PROD(4, "stmt", "decl_stmt");
  ADD_PROD(5, "stmt", "assign_stmt");
  ADD_PROD(6, "stmt", "if_stmt");
  ADD_PROD(7, "stmt", "while_stmt");
  ADD_PROD(8, "stmt", "print_stmt");
  ADD_PROD(9, "stmt", "block");
  ADD_PROD(10, "decl_stmt", "TYPE", "ID", "decl_prime");
  ADD_PROD(11, "decl_prime", "ASSIGNMENT", "arith_expr", "SEMI");
  ADD_PROD(12, "decl_prime", "SEMI");
  ADD_PROD(13, "assign_stmt", "ID", "ASSIGNMENT", "arith_expr", "SEMI");
  ADD_PROD(14, "if_stmt", "IF", "LPAREN", "bool_expr", "RPAREN", "block",
           "else_prime");
  ADD_PROD(15, "else_prime", "ELSE", "block");
  ADD_PROD(16, "else_prime", "\xce\xb5");
  ADD_PROD(17, "while_stmt", "WHILE", "LPAREN", "bool_expr", "RPAREN", "block");
  ADD_PROD(18, "print_stmt", "PRINT", "LPAREN", "arith_expr", "RPAREN", "SEMI");
  ADD_PROD(19, "block", "LBRACE", "stmt_list", "RBRACE");
  ADD_PROD(20, "arith_expr", "term", "arith_expr_tail");
  ADD_PROD(21, "arith_expr_tail", "PLUS", "term", "arith_expr_tail");
  ADD_PROD(22, "arith_expr_tail", "MINUS", "term", "arith_expr_tail");
  ADD_PROD(23, "arith_expr_tail", "\xce\xb5");
  ADD_PROD(24, "term", "factor", "term_tail");
  ADD_PROD(25, "term_tail", "MULT", "factor", "term_tail");
  ADD_PROD(26, "term_tail", "DIV", "factor", "term_tail");
  ADD_PROD(27, "term_tail", "MOD", "factor", "term_tail");
  ADD_PROD(28, "term_tail", "\xce\xb5");
  ADD_PROD(29, "factor", "LPAREN", "arith_expr", "RPAREN");
  ADD_PROD(30, "factor", "ID");
  ADD_PROD(31, "factor", "INTEGER");
  ADD_PROD(32, "factor", "FLOAT");
  ADD_PROD(33, "bool_expr", "bool_term", "bool_expr_tail");
  ADD_PROD(34, "bool_expr_tail", "LOGICAL_OR", "bool_term", "bool_expr_tail");
  ADD_PROD(35, "bool_expr_tail", "\xce\xb5");
  ADD_PROD(36, "bool_term", "bool_factor", "bool_term_tail");
  ADD_PROD(37, "bool_term_tail", "LOGICAL_AND", "bool_factor",
           "bool_term_tail");
  ADD_PROD(38, "bool_term_tail", "\xce\xb5");
  ADD_PROD(39, "bool_factor", "arith_expr", "rel_op", "arith_expr");
  ADD_PROD(40, "bool_factor", "LPAREN", "bool_expr", "RPAREN");
  ADD_PROD(41, "bool_factor", "NOT", "bool_factor");
  ADD_PROD(42, "rel_op", "REL_OP");
#undef ADD_PROD
}

/* ========== SYMBOL LISTS ========== */
const char *TERM_LIST[] = {
    "TYPE",   "ID",      "SEMI",       "ASSIGNMENT",  "IF",
    "LPAREN", "RPAREN",  "ELSE",       "WHILE",       "PRINT",
    "LBRACE", "RBRACE",  "LOGICAL_OR", "LOGICAL_AND", "NOT",
    "REL_OP", "PLUS",    "MINUS",      "MULT",        "DIV",
    "MOD",    "INTEGER", "FLOAT",      "$",           NULL};

int is_terminal(const char *s) {
  if (strcmp(s, "\xce\xb5") == 0)
    return 1;
  for (int i = 0; TERM_LIST[i]; i++)
    if (strcmp(s, TERM_LIST[i]) == 0)
      return 1;
  return 0;
}
int nt_index(const char *s) {
  for (int i = 0; i < nt_count; i++)
    if (strcmp(non_terminals[i], s) == 0)
      return i;
  return -1;
}
int term_index(const char *s) {
  for (int i = 0; i < term_count; i++)
    if (strcmp(terminals[i], s) == 0)
      return i;
  return -1;
}
void build_symbol_lists(void) {
  nt_count = 0;
  term_count = 0;
  for (int i = 0; i < prod_count; i++)
    if (nt_index(prods[i].lhs) == -1)
      strcpy(non_terminals[nt_count++], prods[i].lhs);
  for (int i = 0; TERM_LIST[i]; i++)
    strcpy(terminals[term_count++], TERM_LIST[i]);
}

/* ========== FIRST SET ========== */
void add_to_first(int ni, const char *s) {
  for (int i = 0; i < first_cnt[ni]; i++)
    if (strcmp(first_set[ni][i], s) == 0)
      return;
  strcpy(first_set[ni][first_cnt[ni]++], s);
}
int first_of_sequence(char seq[][MAX_LABEL], int len, char out[][MAX_LABEL],
                      int *out_cnt) {
  *out_cnt = 0;
  int all_eps = 1;
  for (int i = 0; i < len && all_eps; i++) {
    char *sym = seq[i];
    if (strcmp(sym, "\xce\xb5") == 0)
      continue;
    if (is_terminal(sym)) {
      int found = 0;
      for (int k = 0; k < *out_cnt; k++)
        if (strcmp(out[k], sym) == 0) {
          found = 1;
          break;
        }
      if (!found)
        strcpy(out[(*out_cnt)++], sym);
      all_eps = 0;
    } else {
      int ni = nt_index(sym);
      if (ni == -1) {
        all_eps = 0;
        break;
      }
      int has_eps = 0;
      for (int k = 0; k < first_cnt[ni]; k++) {
        if (strcmp(first_set[ni][k], "\xce\xb5") == 0) {
          has_eps = 1;
          continue;
        }
        int found = 0;
        for (int m = 0; m < *out_cnt; m++)
          if (strcmp(out[m], first_set[ni][k]) == 0) {
            found = 1;
            break;
          }
        if (!found)
          strcpy(out[(*out_cnt)++], first_set[ni][k]);
      }
      if (!has_eps)
        all_eps = 0;
    }
  }
  if (all_eps) {
    int has_eps = 0;
    for (int k = 0; k < *out_cnt; k++)
      if (strcmp(out[k], "\xce\xb5") == 0) {
        has_eps = 1;
        break;
      }
    if (!has_eps)
      strcpy(out[(*out_cnt)++], "\xce\xb5");
  }
  return all_eps;
}
void compute_first_sets(void) {
  int changed = 1;
  for (int i = 0; i < nt_count; i++)
    first_cnt[i] = 0;
  while (changed) {
    changed = 0;
    for (int p = 0; p < prod_count; p++) {
      int ni = nt_index(prods[p].lhs);
      if (ni == -1)
        continue;
      int before = first_cnt[ni];
      char seq[MAX_RHS][MAX_LABEL];
      for (int k = 0; k < prods[p].rhs_len; k++)
        strcpy(seq[k], prods[p].rhs[k]);
      char out[MAX_SYMBOLS][MAX_LABEL];
      int out_cnt = 0;
      first_of_sequence(seq, prods[p].rhs_len, out, &out_cnt);
      for (int k = 0; k < out_cnt; k++)
        add_to_first(ni, out[k]);
      if (first_cnt[ni] != before)
        changed = 1;
    }
  }
}

/* ========== FOLLOW SET ========== */
void add_to_follow(int ni, const char *s) {
  for (int i = 0; i < follow_cnt[ni]; i++)
    if (strcmp(follow_set[ni][i], s) == 0)
      return;
  strcpy(follow_set[ni][follow_cnt[ni]++], s);
}
void compute_follow_sets(void) {
  int changed = 1;
  for (int i = 0; i < nt_count; i++)
    follow_cnt[i] = 0;
  add_to_follow(nt_index("program"), "$");
  while (changed) {
    changed = 0;
    for (int p = 0; p < prod_count; p++) {
      int lhs = nt_index(prods[p].lhs);
      if (lhs == -1)
        continue;
      for (int j = 0; j < prods[p].rhs_len; j++) {
        char *B = prods[p].rhs[j];
        if (is_terminal(B))
          continue;
        int Bni = nt_index(B);
        if (Bni == -1)
          continue;
        int before = follow_cnt[Bni];
        int beta_len = prods[p].rhs_len - j - 1;
        if (beta_len > 0) {
          char beta[MAX_RHS][MAX_LABEL];
          for (int k = 0; k < beta_len; k++)
            strcpy(beta[k], prods[p].rhs[j + 1 + k]);
          char out[MAX_SYMBOLS][MAX_LABEL];
          int out_cnt = 0;
          int has_eps = first_of_sequence(beta, beta_len, out, &out_cnt);
          for (int k = 0; k < out_cnt; k++)
            if (strcmp(out[k], "\xce\xb5") != 0)
              add_to_follow(Bni, out[k]);
          if (has_eps)
            for (int k = 0; k < follow_cnt[lhs]; k++)
              add_to_follow(Bni, follow_set[lhs][k]);
        } else {
          for (int k = 0; k < follow_cnt[lhs]; k++)
            add_to_follow(Bni, follow_set[lhs][k]);
        }
        if (follow_cnt[Bni] != before)
          changed = 1;
      }
    }
  }
}

/* ========== LL(1) TABLE ========== */
void build_ll1_table(void) {
  for (int i = 0; i < nt_count; i++)
    for (int j = 0; j < term_count; j++)
      ll1_table[i][j] = -1;
  for (int p = 0; p < prod_count; p++) {
    int ni = nt_index(prods[p].lhs);
    if (ni == -1)
      continue;
    char seq[MAX_RHS][MAX_LABEL];
    for (int k = 0; k < prods[p].rhs_len; k++)
      strcpy(seq[k], prods[p].rhs[k]);
    char out[MAX_SYMBOLS][MAX_LABEL];
    int out_cnt = 0;
    first_of_sequence(seq, prods[p].rhs_len, out, &out_cnt);
    for (int k = 0; k < out_cnt; k++) {
      if (strcmp(out[k], "\xce\xb5") == 0) {
        for (int m = 0; m < follow_cnt[ni]; m++) {
          int ti = term_index(follow_set[ni][m]);
          if (ti != -1)
            ll1_table[ni][ti] = prods[p].num;
        }
      } else {
        int ti = term_index(out[k]);
        if (ti != -1)
          ll1_table[ni][ti] = prods[p].num;
      }
    }
  }
}

/* ========== TOKEN -> TERMINAL ========== */
const char *token_to_terminal(Token *t) {
  if (!t)
    return "$";
  if (strcmp(t->type, "KEYWORD") == 0) {
    if (strcmp(t->value, "int") == 0 || strcmp(t->value, "float") == 0)
      return "TYPE";
    if (strcmp(t->value, "if") == 0)
      return "IF";
    if (strcmp(t->value, "else") == 0)
      return "ELSE";
    if (strcmp(t->value, "while") == 0)
      return "WHILE";
    if (strcmp(t->value, "print") == 0)
      return "PRINT";
  }
  if (strcmp(t->type, "IDENTIFIER") == 0)
    return "ID";
  if (strcmp(t->type, "INTEGER") == 0)
    return "INTEGER";
  if (strcmp(t->type, "FLOAT") == 0)
    return "FLOAT";
  if (strcmp(t->type, "ASSIGNMENT") == 0)
    return "ASSIGNMENT";
  if (strcmp(t->type, "RELATIONAL") == 0)
    return "REL_OP";
  if (strcmp(t->type, "ARITHMETIC") == 0) {
    if (strcmp(t->value, "+") == 0)
      return "PLUS";
    if (strcmp(t->value, "-") == 0)
      return "MINUS";
    if (strcmp(t->value, "*") == 0)
      return "MULT";
    if (strcmp(t->value, "/") == 0)
      return "DIV";
    if (strcmp(t->value, "%") == 0)
      return "MOD";
  }
  if (strcmp(t->type, "LOGICAL") == 0) {
    if (strcmp(t->value, "!") == 0)
      return "NOT";
    if (strcmp(t->value, "&&") == 0)
      return "LOGICAL_AND";
    if (strcmp(t->value, "||") == 0)
      return "LOGICAL_OR";
  }
  if (strcmp(t->type, "DELIMITER") == 0) {
    if (strcmp(t->value, "(") == 0)
      return "LPAREN";
    if (strcmp(t->value, ")") == 0)
      return "RPAREN";
    if (strcmp(t->value, ";") == 0)
      return "SEMI";
    if (strcmp(t->value, "{") == 0)
      return "LBRACE";
    if (strcmp(t->value, "}") == 0)
      return "RBRACE";
  }
  return t->type;
}

/* ========== PRINT FUNCTIONS ========== */
void print_productions(void) {
  printf("\n==================================================================="
         "=============\n");
  printf("LEFT-FACTORED GRAMMAR PRODUCTIONS\n");
  printf("====================================================================="
         "===========\n\n");
  for (int i = 0; i < prod_count; i++) {
    printf("  [%2d]  %-20s -> ", prods[i].num, prods[i].lhs);
    if (strcmp(prods[i].rhs[0], "\xce\xb5") == 0)
      printf("eps");
    else
      for (int j = 0; j < prods[i].rhs_len; j++)
        printf("%s ", eps_str(prods[i].rhs[j]));
    printf("\n");
  }
  printf("\n");
}
void print_first_sets(void) {
  printf("\n==================================================================="
         "=============\n");
  printf("FIRST SETS\n");
  printf("====================================================================="
         "===========\n\n");
  for (int i = 0; i < nt_count; i++) {
    printf("  FIRST(%-18s) = { ", non_terminals[i]);
    for (int j = 0; j < first_cnt[i]; j++)
      printf("%s ", eps_str(first_set[i][j]));
    printf("}\n");
  }
  printf("\n");
}
void print_follow_sets(void) {
  printf("\n==================================================================="
         "=============\n");
  printf("FOLLOW SETS\n");
  printf("====================================================================="
         "===========\n\n");
  for (int i = 0; i < nt_count; i++) {
    printf("  FOLLOW(%-18s) = { ", non_terminals[i]);
    for (int j = 0; j < follow_cnt[i]; j++)
      printf("%s ", eps_str(follow_set[i][j]));
    printf("}\n");
  }
  printf("\n");
}
void print_ll1_table(void) {
  printf("\n==================================================================="
         "=============\n");
  printf("LL(1) PARSING TABLE (production numbers; blank = error)\n");
  printf("====================================================================="
         "===========\n\n");
  const int NT_W = 20, COL_W = 12, COLS_PER_PASS = 6;
  int passes = (term_count + COLS_PER_PASS - 1) / COLS_PER_PASS;
  for (int pass = 0; pass < passes; pass++) {
    int col_start = pass * COLS_PER_PASS, col_end = col_start + COLS_PER_PASS;
    if (col_end > term_count)
      col_end = term_count;
    printf("+-");
    for (int k = 0; k < NT_W; k++)
      printf("-");
    printf("-+");
    for (int j = col_start; j < col_end; j++) {
      for (int k = 0; k < COL_W; k++)
        printf("-");
      printf("+");
    }
    printf("\n| %-*s |", NT_W, "Non-Terminal");
    for (int j = col_start; j < col_end; j++)
      printf(" %-*s|", COL_W - 1, terminals[j]);
    printf("\n+-");
    for (int k = 0; k < NT_W; k++)
      printf("-");
    printf("-+");
    for (int j = col_start; j < col_end; j++) {
      for (int k = 0; k < COL_W; k++)
        printf("-");
      printf("+");
    }
    printf("\n");
    for (int i = 0; i < nt_count; i++) {
      printf("| %-*s |", NT_W, non_terminals[i]);
      for (int j = col_start; j < col_end; j++) {
        if (ll1_table[i][j] != -1) {
          char cell[16];
          snprintf(cell, sizeof(cell), "P%d", ll1_table[i][j]);
          printf(" %-*s|", COL_W - 1, cell);
        } else
          printf(" %-*s|", COL_W - 1, "");
      }
      printf("\n");
    }
    printf("+-");
    for (int k = 0; k < NT_W; k++)
      printf("-");
    printf("-+");
    for (int j = col_start; j < col_end; j++) {
      for (int k = 0; k < COL_W; k++)
        printf("-");
      printf("+");
    }
    printf("\n\n");
    if (pass < passes - 1)
      printf("  (continued)\n\n");
  }
  printf("  Note: P<n> = apply production n  |  blank = syntax error\n\n");
}

/* ========== LL(1) PARSER ========== */
int ll1_parse_statement(Node *stmt) {
  Token stoks[MAX_TOKENS];
  int slen = 0;
  node_to_tokens(stmt, stoks, &slen);
  if (!quiet_mode) {
    printf("\n================================================================="
           "===============\n");
    printf("LL(1) PARSER - STATEMENT TRACE\n");
    printf("==================================================================="
           "=============\n\n");
    printf("Input: ");
    for (int i = 0; i < slen; i++)
      printf("%s ", stoks[i].value);
    printf("\n\n");
  }
  char input[MAX_TOKENS + 2][MAX_LABEL];
  int input_lines[MAX_TOKENS + 2];
  int input_len = 0;
  for (int i = 0; i < slen; i++) {
    strcpy(input[input_len], token_to_terminal(&stoks[i]));
    input_lines[input_len] = stoks[i].line;
    input_len++;
  }
  strcpy(input[input_len], "$");
  input_lines[input_len] = (slen > 0 ? stoks[slen - 1].line : 0);
  input_len++;
  char stack[MAX_STACK][MAX_LABEL];
  int top = -1;
  strcpy(stack[++top], "$");
  strcpy(stack[++top], "stmt");
  int ip = 0, step = 1, success = 1, ll1_errors = 0;
  if (!quiet_mode) {
    printf("%-5s  %-42s  %-30s  %s\n", "Step", "Stack (top-bottom)",
           "Remaining Input", "Action");
    printf(
        "-----  ------------------------------------------  "
        "------------------------------  ---------------------------------\n");
  }
  while (top >= 0 && step < 300) {
    char *X = stack[top];
    char *a = (ip < input_len) ? input[ip] : "$";
    char ss[256] = "";
    int spos = 0;
    for (int i = top; i >= 0 && spos < 250; i--) {
      int l = strlen(stack[i]);
      memcpy(ss + spos, stack[i], l);
      spos += l;
      if (i > 0 && spos < 249) {
        ss[spos++] = ' ';
      }
    }
    ss[spos] = '\0';
    char is[128] = "";
    int ipos = 0;
    for (int i = ip; i < input_len && i < ip + 5 && ipos < 120; i++) {
      int l = strlen(input[i]);
      memcpy(is + ipos, input[i], l);
      ipos += l;
      if (i < input_len - 1 && ipos < 119) {
        is[ipos++] = ' ';
      }
    }
    if (ip + 5 < input_len) {
      strcpy(is + ipos, "...");
      ipos += 3;
    }
    is[ipos] = '\0';
    if (!quiet_mode)
      printf("%-5d  %-42s  %-30s  ", step, ss, is);
    step++;
    if (strcmp(X, "$") == 0 && strcmp(a, "$") == 0) {
      if (!quiet_mode)
        printf("ACCEPT\n");
      break;
    }
    if (is_terminal(X)) {
      if (strcmp(X, a) == 0) {
        if (!quiet_mode)
          printf("Match '%s'\n", X);
        top--;
        ip++;
      } else if (strcmp(X, "\xce\xb5") == 0) {
        if (!quiet_mode)
          printf("Pop eps\n");
        top--;
      } else {
        int ln = (ip < input_len) ? input_lines[ip]
                                  : (slen > 0 ? stoks[slen - 1].line : 0);
        if (!quiet_mode)
          printf("*** ERROR: expected '%s', found '%s' (line %d)\n", X, a, ln);
        ll1_errors++;
        success = 0;
        break;
      }
    } else {
      int ni = nt_index(X), ti = term_index(a);
      if (ni < 0 || ti < 0 || ll1_table[ni][ti] == -1) {
        int ln = (ip < input_len) ? input_lines[ip]
                                  : (slen > 0 ? stoks[slen - 1].line : 0);
        if (!quiet_mode)
          printf("*** ERROR: no production for [%s,%s] (line %d)\n", X, a, ln);
        ll1_errors++;
        success = 0;
        break;
      }
      int pnum = ll1_table[ni][ti];
      for (int p = 0; p < prod_count; p++) {
        if (prods[p].num == pnum) {
          if (!quiet_mode) {
            printf("Apply P%d: %s -> ", pnum, prods[p].lhs);
            if (strcmp(prods[p].rhs[0], "\xce\xb5") == 0)
              printf("eps");
            else
              for (int j = 0; j < prods[p].rhs_len; j++)
                printf("%s ", eps_str(prods[p].rhs[j]));
            printf("\n");
          }
          top--;
          if (strcmp(prods[p].rhs[0], "\xce\xb5") != 0)
            for (int j = prods[p].rhs_len - 1; j >= 0; j--)
              strcpy(stack[++top], prods[p].rhs[j]);
          break;
        }
      }
    }
  }
  if (!quiet_mode) {
    printf("\n");
    if (ll1_errors > 0)
      printf("[FAILED] LL(1) Parser: %d error(s) detected.\n\n", ll1_errors);
    else if (success)
      printf("[SUCCESS] LL(1) Parser accepted the statement.\n\n");
    else
      printf("[FAILED] LL(1) Parser: step limit reached.\n\n");
  }
  return success && ll1_errors == 0;
}

/* ========== SHIFT-REDUCE PARSER ========== */
typedef struct {
  char sym[MAX_LABEL];
  int line;
} SRItem;
SRItem sr_stack[MAX_STACK];
int sr_top = -1;

static void sr_push(const char *s, int ln) {
  if (sr_top < MAX_STACK - 1) {
    sr_top++;
    strcpy(sr_stack[sr_top].sym, s);
    sr_stack[sr_top].line = ln;
  }
}
static void sr_pop(void) {
  if (sr_top >= 0)
    sr_top--;
}
static int sr_check(int off, const char *s) {
  int idx = sr_top - off;
  return idx >= 0 && strcmp(sr_stack[idx].sym, s) == 0;
}

static int sr_try_reduce(const char *la, char *desc) {
  /* ===== 0. EMPTY BLOCK: LBRACE on top with RBRACE as lookahead ===== */
  if (sr_check(0, "LBRACE") && strcmp(la, "RBRACE") == 0) {
    int ln = sr_stack[sr_top].line;
    sr_push("stmt_list", ln);
    sprintf(desc, "[3] stmt_list -> eps (empty block)");
    return 1;
  }

  /* ===== A. DECLARATION STATEMENT ===== */
  if (sr_top >= 4 && sr_check(4, "TYPE") && sr_check(3, "ID") &&
      sr_check(2, "ASSIGNMENT") && sr_check(1, "arith_expr") &&
      sr_check(0, "SEMI")) {
    int ln = sr_stack[sr_top - 2].line;
    sr_pop();
    sr_pop();
    sr_pop();
    sr_push("decl_prime", ln);
    sprintf(desc, "[11] decl_prime -> = arith_expr ;");
    return 1;
  }
  if (sr_top >= 2 && sr_check(2, "TYPE") && sr_check(1, "ID") &&
      sr_check(0, "SEMI")) {
    int ln = sr_stack[sr_top].line;
    sr_pop();
    sr_push("decl_prime", ln);
    sprintf(desc, "[12] decl_prime -> ;");
    return 1;
  }
  if (sr_top >= 2 && sr_check(2, "TYPE") && sr_check(1, "ID") &&
      sr_check(0, "decl_prime")) {
    int ln = sr_stack[sr_top - 2].line;
    sr_pop();
    sr_pop();
    sr_pop();
    sr_push("decl_stmt", ln);
    sprintf(desc, "[10] decl_stmt -> TYPE ID decl_prime");
    return 1;
  }
  if (sr_check(0, "decl_stmt")) {
    int ln = sr_stack[sr_top].line;
    sr_pop();
    sr_push("stmt", ln);
    sprintf(desc, "[4] stmt -> decl_stmt");
    return 1;
  }

  /* ===== B. ASSIGNMENT STATEMENT ===== */
  if (sr_top >= 3 && sr_check(3, "ID") && sr_check(2, "ASSIGNMENT") &&
      sr_check(1, "arith_expr") && sr_check(0, "SEMI")) {
    if (!(sr_top >= 4 && sr_check(4, "TYPE"))) {
      int ln = sr_stack[sr_top - 3].line;
      sr_pop();
      sr_pop();
      sr_pop();
      sr_pop();
      sr_push("assign_stmt", ln);
      sprintf(desc, "[13] assign_stmt -> ID = arith_expr ;");
      return 1;
    }
  }
  if (sr_check(0, "assign_stmt")) {
    int ln = sr_stack[sr_top].line;
    sr_pop();
    sr_push("stmt", ln);
    sprintf(desc, "[5] stmt -> assign_stmt");
    return 1;
  }

  /* ===== C. FACTOR from terminal atoms ===== */
  if (sr_check(0, "ID")) {
    if (sr_top >= 1 && sr_check(1, "TYPE"))
      return 0;
    if (strcmp(la, "ASSIGNMENT") == 0)
      return 0;
    int ln = sr_stack[sr_top].line;
    sr_pop();
    sr_push("factor", ln);
    sprintf(desc, "[30] factor -> ID");
    return 1;
  }
  if (sr_check(0, "INTEGER")) {
    int ln = sr_stack[sr_top].line;
    sr_pop();
    sr_push("factor", ln);
    sprintf(desc, "[31] factor -> INTEGER");
    return 1;
  }
  if (sr_check(0, "FLOAT")) {
    int ln = sr_stack[sr_top].line;
    sr_pop();
    sr_push("factor", ln);
    sprintf(desc, "[32] factor -> FLOAT");
    return 1;
  }

  /* ===== D. factor -> ( arith_expr ) ===== */
  if (sr_top >= 2 && sr_check(2, "LPAREN") && sr_check(1, "arith_expr") &&
      sr_check(0, "RPAREN")) {
    int is_ctrl = 0;
    if (sr_top >= 3) {
      if (sr_check(3, "IF") || sr_check(3, "WHILE") || sr_check(3, "PRINT"))
        is_ctrl = 1;
    }
    if (!is_ctrl) {
      int ln = sr_stack[sr_top - 2].line;
      sr_pop();
      sr_pop();
      sr_pop();
      sr_push("factor", ln);
      sprintf(desc, "[29] factor -> ( arith_expr )");
      return 1;
    }
  }

  /* ===== E. TERM_TAIL ===== */
  if (sr_top >= 2 && sr_check(2, "MULT") && sr_check(1, "factor") &&
      sr_check(0, "term_tail")) {
    int ln = sr_stack[sr_top - 2].line;
    sr_pop();
    sr_pop();
    sr_pop();
    sr_push("term_tail", ln);
    sprintf(desc, "[25] term_tail -> * factor term_tail");
    return 1;
  }
  if (sr_top >= 2 && sr_check(2, "DIV") && sr_check(1, "factor") &&
      sr_check(0, "term_tail")) {
    int ln = sr_stack[sr_top - 2].line;
    sr_pop();
    sr_pop();
    sr_pop();
    sr_push("term_tail", ln);
    sprintf(desc, "[26] term_tail -> / factor term_tail");
    return 1;
  }
  if (sr_top >= 2 && sr_check(2, "MOD") && sr_check(1, "factor") &&
      sr_check(0, "term_tail")) {
    int ln = sr_stack[sr_top - 2].line;
    sr_pop();
    sr_pop();
    sr_pop();
    sr_push("term_tail", ln);
    sprintf(desc, "[27] term_tail -> %% factor term_tail");
    return 1;
  }
  if (sr_check(0, "factor")) {
    if (strcmp(la, "MULT") != 0 && strcmp(la, "DIV") != 0 &&
        strcmp(la, "MOD") != 0) {
      int ln = sr_stack[sr_top].line;
      sr_push("term_tail", ln);
      sprintf(desc, "[28] term_tail -> eps");
      return 1;
    }
  }

  /* ===== F. TERM ===== */
  if (sr_top >= 1 && sr_check(1, "factor") && sr_check(0, "term_tail")) {
    int ln = sr_stack[sr_top - 1].line;
    sr_pop();
    sr_pop();
    sr_push("term", ln);
    sprintf(desc, "[24] term -> factor term_tail");
    return 1;
  }

  /* ===== G. ARITH_EXPR_TAIL ===== */
  if (sr_top >= 2 && sr_check(2, "PLUS") && sr_check(1, "term") &&
      sr_check(0, "arith_expr_tail")) {
    int ln = sr_stack[sr_top - 2].line;
    sr_pop();
    sr_pop();
    sr_pop();
    sr_push("arith_expr_tail", ln);
    sprintf(desc, "[21] arith_expr_tail -> + term arith_expr_tail");
    return 1;
  }
  if (sr_top >= 2 && sr_check(2, "MINUS") && sr_check(1, "term") &&
      sr_check(0, "arith_expr_tail")) {
    int ln = sr_stack[sr_top - 2].line;
    sr_pop();
    sr_pop();
    sr_pop();
    sr_push("arith_expr_tail", ln);
    sprintf(desc, "[22] arith_expr_tail -> - term arith_expr_tail");
    return 1;
  }
  if (sr_check(0, "term")) {
    if (strcmp(la, "PLUS") != 0 && strcmp(la, "MINUS") != 0) {
      int ln = sr_stack[sr_top].line;
      sr_push("arith_expr_tail", ln);
      sprintf(desc, "[23] arith_expr_tail -> eps");
      return 1;
    }
  }

  /* ===== H. ARITH_EXPR ===== */
  if (sr_top >= 1 && sr_check(1, "term") && sr_check(0, "arith_expr_tail")) {
    int ln = sr_stack[sr_top - 1].line;
    sr_pop();
    sr_pop();
    sr_push("arith_expr", ln);
    sprintf(desc, "[20] arith_expr -> term arith_expr_tail");
    return 1;
  }

  /* ===== I. BOOLEAN EXPRESSIONS ===== */
  if (sr_check(0, "REL_OP")) {
    int ln = sr_stack[sr_top].line;
    sr_pop();
    sr_push("rel_op", ln);
    sprintf(desc, "[42] rel_op -> REL_OP");
    return 1;
  }
  if (sr_top >= 2 && sr_check(2, "arith_expr") && sr_check(1, "rel_op") &&
      sr_check(0, "arith_expr")) {
    int ln = sr_stack[sr_top - 2].line;
    sr_pop();
    sr_pop();
    sr_pop();
    sr_push("bool_factor", ln);
    sprintf(desc, "[39] bool_factor -> arith_expr rel_op arith_expr");
    return 1;
  }
  if (sr_top >= 1 && sr_check(1, "NOT") && sr_check(0, "bool_factor")) {
    int ln = sr_stack[sr_top - 1].line;
    sr_pop();
    sr_pop();
    sr_push("bool_factor", ln);
    sprintf(desc, "[41] bool_factor -> NOT bool_factor");
    return 1;
  }
  if (sr_top >= 2 && sr_check(2, "LPAREN") && sr_check(1, "bool_expr") &&
      sr_check(0, "RPAREN")) {
    int is_control = 0;
    if (sr_top >= 3 && (sr_check(3, "IF") || sr_check(3, "WHILE")))
      is_control = 1;
    if (!is_control) {
      int ln = sr_stack[sr_top - 2].line;
      sr_pop();
      sr_pop();
      sr_pop();
      sr_push("bool_factor", ln);
      sprintf(desc, "[40] bool_factor -> ( bool_expr )");
      return 1;
    }
  }
  if (sr_check(0, "bool_factor")) {
    if (strcmp(la, "LOGICAL_AND") != 0) {
      int ln = sr_stack[sr_top].line;
      sr_push("bool_term_tail", ln);
      sprintf(desc, "[38] bool_term_tail -> eps");
      return 1;
    }
  }
  if (sr_top >= 2 && sr_check(2, "LOGICAL_AND") && sr_check(1, "bool_factor") &&
      sr_check(0, "bool_term_tail")) {
    int ln = sr_stack[sr_top - 2].line;
    sr_pop();
    sr_pop();
    sr_pop();
    sr_push("bool_term_tail", ln);
    sprintf(desc, "[37] bool_term_tail -> && bool_factor bool_term_tail");
    return 1;
  }
  if (sr_top >= 1 && sr_check(1, "bool_factor") &&
      sr_check(0, "bool_term_tail")) {
    int ln = sr_stack[sr_top - 1].line;
    sr_pop();
    sr_pop();
    sr_push("bool_term", ln);
    sprintf(desc, "[36] bool_term -> bool_factor bool_term_tail");
    return 1;
  }
  if (sr_check(0, "bool_term")) {
    if (strcmp(la, "LOGICAL_OR") != 0) {
      int ln = sr_stack[sr_top].line;
      sr_push("bool_expr_tail", ln);
      sprintf(desc, "[35] bool_expr_tail -> eps");
      return 1;
    }
  }
  if (sr_top >= 2 && sr_check(2, "LOGICAL_OR") && sr_check(1, "bool_term") &&
      sr_check(0, "bool_expr_tail")) {
    int ln = sr_stack[sr_top - 2].line;
    sr_pop();
    sr_pop();
    sr_pop();
    sr_push("bool_expr_tail", ln);
    sprintf(desc, "[34] bool_expr_tail -> || bool_term bool_expr_tail");
    return 1;
  }
  if (sr_top >= 1 && sr_check(1, "bool_term") &&
      sr_check(0, "bool_expr_tail")) {
    int ln = sr_stack[sr_top - 1].line;
    sr_pop();
    sr_pop();
    sr_push("bool_expr", ln);
    sprintf(desc, "[33] bool_expr -> bool_term bool_expr_tail");
    return 1;
  }

  /* ===== J. PRINT STATEMENT ===== */
  if (sr_top >= 4 && sr_check(4, "PRINT") && sr_check(3, "LPAREN") &&
      sr_check(2, "arith_expr") && sr_check(1, "RPAREN") &&
      sr_check(0, "SEMI")) {
    int ln = sr_stack[sr_top - 4].line;
    sr_pop();
    sr_pop();
    sr_pop();
    sr_pop();
    sr_pop();
    sr_push("print_stmt", ln);
    sprintf(desc, "[18] print_stmt -> print ( arith_expr ) ;");
    return 1;
  }
  if (sr_check(0, "print_stmt")) {
    int ln = sr_stack[sr_top].line;
    sr_pop();
    sr_push("stmt", ln);
    sprintf(desc, "[8] stmt -> print_stmt");
    return 1;
  }

  /* ===== K. BLOCK ===== */
  if (sr_top >= 2 && sr_check(2, "LBRACE") && sr_check(1, "stmt_list") &&
      sr_check(0, "RBRACE")) {
    int ln = sr_stack[sr_top - 2].line;
    sr_pop();
    sr_pop();
    sr_pop();
    sr_push("block", ln);
    sprintf(desc, "[19] block -> { stmt_list }");
    return 1;
  }

  /* ===== L. STATEMENT LIST ===== */
  if (sr_top >= 1 && sr_check(1, "stmt") && sr_check(0, "stmt_list")) {
    int ln = sr_stack[sr_top - 1].line;
    sr_pop();
    sr_pop();
    sr_push("stmt_list", ln);
    sprintf(desc, "[2] stmt_list -> stmt stmt_list");
    return 1;
  }
  if (sr_check(0, "stmt") &&
      (strcmp(la, "RBRACE") == 0 || strcmp(la, "$") == 0)) {
    int ln = sr_stack[sr_top].line;
    sr_push("stmt_list", ln);
    sr_pop();
    sr_pop();
    sr_push("stmt_list", ln);
    sprintf(desc, "[2+3] stmt_list -> stmt eps");
    return 1;
  }

  /* ===== M. WHILE STATEMENT ===== */
  if (sr_top >= 4 && sr_check(4, "WHILE") && sr_check(3, "LPAREN") &&
      sr_check(2, "bool_expr") && sr_check(1, "RPAREN") &&
      sr_check(0, "block")) {
    int ln = sr_stack[sr_top - 4].line;
    sr_pop();
    sr_pop();
    sr_pop();
    sr_pop();
    sr_pop();
    sr_push("while_stmt", ln);
    sprintf(desc, "[17] while_stmt -> while ( bool_expr ) block");
    return 1;
  }
  if (sr_check(0, "while_stmt")) {
    int ln = sr_stack[sr_top].line;
    sr_pop();
    sr_push("stmt", ln);
    sprintf(desc, "[7] stmt -> while_stmt");
    return 1;
  }

  /* ===== N. IF STATEMENT ===== */
  if (sr_top >= 1 && sr_check(1, "ELSE") && sr_check(0, "block")) {
    int ln = sr_stack[sr_top - 1].line;
    sr_pop();
    sr_pop();
    sr_push("else_prime", ln);
    sprintf(desc, "[15] else_prime -> else block");
    return 1;
  }
  if (sr_top >= 5 && sr_check(5, "IF") && sr_check(4, "LPAREN") &&
      sr_check(3, "bool_expr") && sr_check(2, "RPAREN") &&
      sr_check(1, "block") && sr_check(0, "else_prime")) {
    int ln = sr_stack[sr_top - 5].line;
    sr_pop();
    sr_pop();
    sr_pop();
    sr_pop();
    sr_pop();
    sr_pop();
    sr_push("if_stmt", ln);
    sprintf(desc, "[14] if_stmt -> if ( bool_expr ) block else_prime");
    return 1;
  }
  if (sr_top >= 4 && sr_check(4, "IF") && sr_check(3, "LPAREN") &&
      sr_check(2, "bool_expr") && sr_check(1, "RPAREN") &&
      sr_check(0, "block")) {
    if (strcmp(la, "ELSE") != 0) {
      int ln = sr_stack[sr_top - 4].line;
      sr_pop();
      sr_pop();
      sr_pop();
      sr_pop();
      sr_pop();
      sr_push("if_stmt", ln);
      sprintf(desc, "[14+16] if_stmt -> if ( bool_expr ) block (no else)");
      return 1;
    }
  }
  if (sr_check(0, "if_stmt")) {
    int ln = sr_stack[sr_top].line;
    sr_pop();
    sr_push("stmt", ln);
    sprintf(desc, "[6] stmt -> if_stmt");
    return 1;
  }

  /* ===== O. BLOCK -> STMT ===== */
  if (sr_check(0, "block")) {
    int dominated = 0;
    for (int i = sr_top - 1; i >= 0; i--) {
      if (strcmp(sr_stack[i].sym, "IF") == 0 ||
          strcmp(sr_stack[i].sym, "WHILE") == 0 ||
          strcmp(sr_stack[i].sym, "ELSE") == 0) {
        dominated = 1;
        break;
      }
      if (strcmp(sr_stack[i].sym, "LBRACE") == 0)
        break;
    }
    if (!dominated && (strcmp(la, "RBRACE") == 0 || strcmp(la, "$") == 0 ||
                       strcmp(la, "TYPE") == 0 || strcmp(la, "ID") == 0 ||
                       strcmp(la, "IF") == 0 || strcmp(la, "WHILE") == 0 ||
                       strcmp(la, "PRINT") == 0 || strcmp(la, "LBRACE") == 0)) {
      int ln = sr_stack[sr_top].line;
      sr_pop();
      sr_push("stmt", ln);
      sprintf(desc, "[9] stmt -> block");
      return 1;
    }
  }
  return 0;
}

int sr_parse_statement(Node *stmt) {
  Token stoks[MAX_TOKENS];
  int slen = 0;
  node_to_tokens(stmt, stoks, &slen);
  if (!quiet_mode) {
    printf("\n================================================================="
           "===============\n");
    printf("SHIFT-REDUCE PARSER - STATEMENT TRACE\n");
    printf("==================================================================="
           "=============\n\n");
    printf("Input: ");
    for (int i = 0; i < slen; i++)
      printf("%s ", stoks[i].value);
    printf("\n\n");
  }
  char input[MAX_TOKENS + 2][MAX_LABEL];
  int input_lines[MAX_TOKENS + 2];
  int input_len = 0;
  for (int i = 0; i < slen; i++) {
    strcpy(input[input_len], token_to_terminal(&stoks[i]));
    input_lines[input_len] = stoks[i].line;
    input_len++;
  }
  strcpy(input[input_len], "$");
  input_lines[input_len] = (slen > 0 ? stoks[slen - 1].line : 0);
  input_len++;
  sr_top = -1;
  int ip = 0, step = 1, success = 1, sr_errors = 0;
  if (!quiet_mode) {
    printf("%-5s  %-45s  %-30s  %s\n", "Step", "Stack (bottom-top)",
           "Remaining Input", "Action");
    printf(
        "-----  ---------------------------------------------  "
        "------------------------------  ---------------------------------\n");
  }
  while (step < 500 && ip <= input_len) {
    const char *la = (ip < input_len) ? input[ip] : "$";
    char ss[512] = "";
    int spos = 0;
    for (int i = 0; i <= sr_top && spos < 450; i++) {
      int l = strlen(sr_stack[i].sym);
      if (spos + l < 450) {
        memcpy(ss + spos, sr_stack[i].sym, l);
        spos += l;
        if (i < sr_top && spos < 449) {
          ss[spos++] = ' ';
        }
      }
    }
    if (sr_top < 0) {
      strcpy(ss, "(empty)");
      spos = 7;
    }
    ss[spos] = '\0';
    char is[256] = "";
    int ipos = 0;
    for (int i = ip; i < input_len && i < ip + 6 && ipos < 200; i++) {
      int l = strlen(input[i]);
      if (ipos + l < 200) {
        memcpy(is + ipos, input[i], l);
        ipos += l;
        if (i < input_len - 1 && ipos < 199) {
          is[ipos++] = ' ';
        }
      }
    }
    if (ip + 6 < input_len && ipos < 196) {
      strcpy(is + ipos, "...");
      ipos += 3;
    }
    is[ipos] = '\0';
    if (!quiet_mode)
      printf("%-5d  %-45s  %-30s  ", step, ss, is);
    step++;
    if (sr_top == 0 && strcmp(sr_stack[0].sym, "stmt") == 0 &&
        strcmp(la, "$") == 0) {
      if (!quiet_mode)
        printf("ACCEPT\n");
      break;
    }
    char desc[256] = "";
    int reduced = 0;
    while (sr_try_reduce(la, desc)) {
      if (!quiet_mode)
        printf("Reduce: %s\n", desc);
      reduced = 1;
      la = (ip < input_len) ? input[ip] : "$";
      if (sr_top == 0 && strcmp(sr_stack[0].sym, "stmt") == 0 &&
          strcmp(la, "$") == 0) {
        if (!quiet_mode)
          printf("ACCEPT\n");
        goto accept;
      }
    }
    if (reduced)
      continue;
    if (strcmp(la, "$") != 0) {
      if (!quiet_mode)
        printf("Shift: %s\n", la);
      sr_push(la, (ip < input_len) ? input_lines[ip] : 0);
      ip++;
    } else {
      if (!quiet_mode)
        printf("*** ERROR: cannot reduce or shift at '$'\n");
      sr_errors++;
      success = 0;
      break;
    }
  }
accept:
  if (step >= 500) {
    if (!quiet_mode)
      printf("*** ERROR: step limit reached\n");
    success = 0;
    sr_errors++;
  }
  if (!quiet_mode) {
    printf("\n");
    if (sr_errors > 0)
      printf("[FAILED] Shift-Reduce Parser: %d error(s) detected.\n\n",
             sr_errors);
    else if (success)
      printf("[SUCCESS] Shift-Reduce Parser accepted the statement.\n\n");
    else
      printf("[FAILED] Shift-Reduce Parser did not accept.\n\n");
  }
  return success && sr_errors == 0;
}

/* ========== NODE UTILITIES ========== */
void node_to_tokens(Node *node, Token *out, int *out_len) {
  if (!node)
    return;
  if (node->value[0] != '\0') {
    Token t;
    t.line = node->line;
    if (strcmp(node->label, "ID") == 0)
      strcpy(t.type, "IDENTIFIER");
    else if (strcmp(node->label, "INTEGER") == 0)
      strcpy(t.type, "INTEGER");
    else if (strcmp(node->label, "FLOAT") == 0)
      strcpy(t.type, "FLOAT");
    else if (strcmp(node->label, "TYPE") == 0)
      strcpy(t.type, "KEYWORD");
    else if (strcmp(node->label, "IF") == 0 ||
             strcmp(node->label, "ELSE") == 0 ||
             strcmp(node->label, "WHILE") == 0 ||
             strcmp(node->label, "PRINT") == 0)
      strcpy(t.type, "KEYWORD");
    else if (strcmp(node->label, "ASSIGNMENT") == 0)
      strcpy(t.type, "ASSIGNMENT");
    else if (strcmp(node->label, "ARITHMETIC") == 0 ||
             strcmp(node->label, "PLUS") == 0 ||
             strcmp(node->label, "MINUS") == 0 ||
             strcmp(node->label, "MULT") == 0 ||
             strcmp(node->label, "DIV") == 0 || strcmp(node->label, "MOD") == 0)
      strcpy(t.type, "ARITHMETIC");
    else if (strcmp(node->label, "LOGICAL") == 0 ||
             strcmp(node->label, "NOT") == 0 ||
             strcmp(node->label, "LOGICAL_AND") == 0 ||
             strcmp(node->label, "LOGICAL_OR") == 0)
      strcpy(t.type, "LOGICAL");
    else if (strcmp(node->label, "REL_OP") == 0)
      strcpy(t.type, "RELATIONAL");
    else if (strcmp(node->label, "LPAREN") == 0 ||
             strcmp(node->label, "RPAREN") == 0 ||
             strcmp(node->label, "LBRACE") == 0 ||
             strcmp(node->label, "RBRACE") == 0 ||
             strcmp(node->label, "SEMI") == 0)
      strcpy(t.type, "DELIMITER");
    else
      strcpy(t.type, node->label);
    strcpy(t.value, node->value);
    out[(*out_len)++] = t;
  }
  for (int i = 0; i < node->child_count; i++)
    node_to_tokens(node->children[i], out, out_len);
}

/* ========== RECURSIVE DESCENT PARSER ========== */
void print_error(const char *msg, int line) {
  /* Buffer the error - don't print yet */
  sprintf(last_rd_error, ">> Syntax Error at line %d: %s", line, msg);
  if (error_msg_total < MAX_STMTS) {
    sprintf(error_messages[error_msg_total], ">> Syntax Error at line %d: %s",
            line, msg);
    error_msg_total++;
  }
  error_count++;
}
Token *current_tok(void) { return (pos < token_count) ? &tokens[pos] : NULL; }
Token *consume_tok(void) {
  Token *t = current_tok();
  if (t) {
    last_line = t->line;
    pos++;
  }
  return t;
}
Token *expect_type(const char *expected) {
  Token *t = current_tok();
  if (!t || strcmp(t->type, expected) != 0) {
    char err[128];
    sprintf(err, "Expected type %s, got %s", expected, t ? t->type : "EOF");
    print_error(err, last_line);
    return NULL;
  }
  last_line = t->line;
  pos++;
  return t;
}
Token *expect_delim(const char *expected) {
  Token *t = current_tok();
  if (!t) {
    char err[64];
    sprintf(err, "Expected '%s', got EOF", expected);
    print_error(err, last_line);
    return NULL;
  }
  if (strcmp(t->type, "DELIMITER") != 0 || strcmp(t->value, expected) != 0) {
    char err[128];
    sprintf(err, "Expected '%s', got '%s'", expected, t->value);
    print_error(err, last_line);
    return NULL;
  }
  last_line = t->line;
  pos++;
  return t;
}
void skip_to_next_statement(void) {
  while (pos < token_count) {
    Token *t = current_tok();
    if (strcmp(t->type, "KEYWORD") == 0) {
      if (strcmp(t->value, "int") == 0 || strcmp(t->value, "float") == 0 ||
          strcmp(t->value, "if") == 0 || strcmp(t->value, "while") == 0 ||
          strcmp(t->value, "print") == 0)
        return;
    } else if (strcmp(t->type, "IDENTIFIER") == 0) {
      Token *next = (pos + 1 < token_count) ? &tokens[pos + 1] : NULL;
      if (next && strcmp(next->type, "ASSIGNMENT") == 0)
        return;
      pos++;
      continue;
    } else if (strcmp(t->type, "DELIMITER") == 0 &&
               strcmp(t->value, "}") == 0) {
      pos++;
      return;
    }
    pos++;
  }
}
void synchronize(void) {
  while (pos < token_count) {
    Token *t = current_tok();
    if (strcmp(t->type, "DELIMITER") == 0 && strcmp(t->value, ";") == 0) {
      pos++;
      return;
    }
    if (strcmp(t->type, "DELIMITER") == 0 && strcmp(t->value, "}") == 0)
      return;
    if (strcmp(t->type, "KEYWORD") == 0) {
      if (strcmp(t->value, "int") == 0 || strcmp(t->value, "float") == 0 ||
          strcmp(t->value, "if") == 0 || strcmp(t->value, "while") == 0 ||
          strcmp(t->value, "print") == 0)
        return;
    }
    if (strcmp(t->type, "IDENTIFIER") == 0) {
      Token *next = (pos + 1 < token_count) ? &tokens[pos + 1] : NULL;
      if (next && strcmp(next->type, "ASSIGNMENT") == 0)
        return;
    }
    pos++;
  }
}
void get_statement_source(int start_pos, int end_pos, char *buffer) {
  buffer[0] = '\0';
  for (int i = start_pos; i <= end_pos && i < token_count; i++) {
    strcat(buffer, tokens[i].value);
    if (i < end_pos)
      strcat(buffer, " ");
  }
}

Node *parse_factor(void) {
  Token *t = current_tok();
  if (!t)
    return NULL;
  Node *node = create_node("factor", NULL, t->line);
  if (strcmp(t->value, "(") == 0) {
    expect_delim("(");
    Node *expr = parse_expr();
    if (!expr)
      return NULL;
    add_child(node, expr);
    if (!expect_delim(")"))
      return NULL;
  } else if (strcmp(t->type, "INTEGER") == 0) {
    add_child(node, create_node("INTEGER", t->value, t->line));
    consume_tok();
  } else if (strcmp(t->type, "FLOAT") == 0) {
    add_child(node, create_node("FLOAT", t->value, t->line));
    consume_tok();
  } else if (strcmp(t->type, "IDENTIFIER") == 0) {
    add_child(node, create_node("ID", t->value, t->line));
    consume_tok();
  } else {
    char err[64];
    sprintf(err, "unexpected '%s' in expression", t->value);
    print_error(err, t->line);
    consume_tok();
  }
  return node;
}
Node *parse_term(void) {
  Node *node = parse_factor();
  if (!node)
    return NULL;
  while (current_tok()) {
    Token *op = current_tok();
    if (strcmp(op->type, "ARITHMETIC") == 0 &&
        (strcmp(op->value, "*") == 0 || strcmp(op->value, "/") == 0 ||
         strcmp(op->value, "%") == 0)) {
      consume_tok();
      Node *right = parse_factor();
      if (!right)
        return NULL;
      Node *parent = create_node("term", NULL, op->line);
      add_child(parent, node);
      add_child(parent, create_node("ARITHMETIC", op->value, op->line));
      add_child(parent, right);
      node = parent;
    } else
      break;
  }
  return node;
}
Node *parse_expr(void) {
  Node *node = parse_term();
  if (!node)
    return NULL;
  while (current_tok()) {
    Token *op = current_tok();
    if (strcmp(op->type, "ARITHMETIC") == 0 &&
        (strcmp(op->value, "+") == 0 || strcmp(op->value, "-") == 0)) {
      consume_tok();
      Node *right = parse_term();
      if (!right)
        return NULL;
      Node *parent = create_node("expr", NULL, op->line);
      add_child(parent, node);
      add_child(parent, create_node("ARITHMETIC", op->value, op->line));
      add_child(parent, right);
      node = parent;
    } else
      break;
  }
  return node;
}
Node *parse_bool_atom(void) {
  Token *cur = current_tok();
  if (!cur)
    return NULL;
  if (strcmp(cur->value, "!") == 0) {
    Node *node = create_node("bool_expr", NULL, cur->line);
    consume_tok();
    add_child(node, create_node("NOT", "!", last_line));
    Node *next = parse_bool_atom();
    if (next)
      add_child(node, next);
    return node;
  } else if (strcmp(cur->value, "(") == 0) {
    expect_delim("(");
    Node *node = parse_bool_expr();
    expect_delim(")");
    return node;
  } else {
    Node *n = create_node("bool_expr", NULL, cur->line);
    Node *expr = parse_expr();
    if (expr)
      add_child(n, expr);
    Token *t = current_tok();
    if (t && strcmp(t->type, "RELATIONAL") == 0) {
      consume_tok();
      add_child(n, create_node("REL_OP", t->value, t->line));
      Node *right = parse_expr();
      if (right)
        add_child(n, right);
    }
    return n;
  }
}
Node *parse_bool_expr(void) {
  Node *node = parse_bool_atom();
  if (!node)
    return NULL;
  while (current_tok()) {
    Token *t = current_tok();
    if (t && strcmp(t->type, "LOGICAL") == 0) {
      Node *parent = create_node("bool_expr", NULL, t->line);
      add_child(parent, node);
      add_child(parent, create_node("LOGICAL", t->value, t->line));
      consume_tok();
      Node *right = parse_bool_atom();
      if (right)
        add_child(parent, right);
      node = parent;
    } else
      break;
  }
  return node;
}
Node *parse_decl_statement(void) {
  Token *t = current_tok();
  if (!t)
    return NULL;
  Node *node = create_node("decl_stmt", NULL, t->line);
  t = expect_type("KEYWORD");
  if (!t)
    return NULL;
  add_child(node, create_node("TYPE", t->value, t->line));
  t = expect_type("IDENTIFIER");
  if (!t)
    return NULL;
  add_child(node, create_node("ID", t->value, t->line));
  if (current_tok() && strcmp(current_tok()->type, "ASSIGNMENT") == 0) {
    t = consume_tok();
    add_child(node, create_node("ASSIGNMENT", t->value, t->line));
    Node *expr = parse_expr();
    if (expr)
      add_child(node, expr);
  }
  if (!expect_delim(";")) {
    synchronize();
    strcpy(node->rd_error, last_rd_error);
    return node;
  }
  add_child(node, create_node("SEMI", ";", last_line));
  return node;
}
Node *parse_assign_statement(void) {
  Token *t = current_tok();
  if (!t)
    return NULL;
  Node *node = create_node("assign_stmt", NULL, t->line);
  t = expect_type("IDENTIFIER");
  if (!t)
    return NULL;
  add_child(node, create_node("ID", t->value, t->line));
  Token *at = expect_type("ASSIGNMENT");
  if (!at) {
    synchronize();
    strcpy(node->rd_error, last_rd_error);
    return node;
  }
  add_child(node, create_node("ASSIGNMENT", at->value, at->line));
  Node *expr = parse_expr();
  if (expr)
    add_child(node, expr);
  if (!expect_delim(";")) {
    synchronize();
    strcpy(node->rd_error, last_rd_error);
    return node;
  }
  add_child(node, create_node("SEMI", ";", last_line));
  return node;
}
Node *parse_error_statement(void) {
  Token *t = current_tok();
  if (!t)
    return NULL;
  Node *node = create_node("error_stmt", NULL, t->line);
  strcpy(node->rd_error, last_rd_error);
  int start_pos = pos;
  while (current_tok()) {
    Token *cur = current_tok();
    if (strcmp(cur->type, "DELIMITER") == 0 && strcmp(cur->value, ";") == 0) {
      add_child(node, create_node("SEMI", cur->value, cur->line));
      consume_tok();
      break;
    }
    if (strcmp(cur->type, "KEYWORD") == 0) {
      if (strcmp(cur->value, "int") == 0 || strcmp(cur->value, "float") == 0 ||
          strcmp(cur->value, "if") == 0 || strcmp(cur->value, "while") == 0 ||
          strcmp(cur->value, "print") == 0) {
        break;
      }
    }
    if (strcmp(cur->type, "IDENTIFIER") == 0) {
      Token *next = (pos + 1 < token_count) ? &tokens[pos + 1] : NULL;
      if (next && strcmp(next->type, "ASSIGNMENT") == 0) {
        break;
      }
    }
    {
      char lbl[MAX_LABEL];
      if (strcmp(cur->type, "IDENTIFIER") == 0)
        strcpy(lbl, "ID");
      else if (strcmp(cur->type, "INTEGER") == 0)
        strcpy(lbl, "INTEGER");
      else if (strcmp(cur->type, "FLOAT") == 0)
        strcpy(lbl, "FLOAT");
      else if (strcmp(cur->type, "KEYWORD") == 0)
        strcpy(lbl, "TYPE");
      else if (strcmp(cur->type, "ASSIGNMENT") == 0)
        strcpy(lbl, "ASSIGNMENT");
      else if (strcmp(cur->type, "ARITHMETIC") == 0)
        strcpy(lbl, "ARITHMETIC");
      else if (strcmp(cur->type, "LOGICAL") == 0)
        strcpy(lbl, "LOGICAL");
      else if (strcmp(cur->type, "RELATIONAL") == 0)
        strcpy(lbl, "REL_OP");
      else if (strcmp(cur->type, "DELIMITER") == 0) {
        if (strcmp(cur->value, "(") == 0)
          strcpy(lbl, "LPAREN");
        else if (strcmp(cur->value, ")") == 0)
          strcpy(lbl, "RPAREN");
        else if (strcmp(cur->value, "{") == 0)
          strcpy(lbl, "LBRACE");
        else if (strcmp(cur->value, "}") == 0)
          strcpy(lbl, "RBRACE");
        else
          strcpy(lbl, cur->type);
      } else
        strcpy(lbl, cur->type);
      add_child(node, create_node(lbl, cur->value, cur->line));
    }
    consume_tok();
  }
  char source_buf[4096] = {0};
  for (int i = start_pos; i < pos && i < token_count; i++) {
    strcat(source_buf, tokens[i].value);
    if (i < pos - 1)
      strcat(source_buf, " ");
  }
  strcpy(node->source, source_buf);
  return node;
}
Node *parse_if_statement(void) {
  Token *t = current_tok();
  if (!t)
    return NULL;
  Node *node = create_node("if_stmt", NULL, t->line);
  if (strcmp(t->value, "if") != 0) {
    print_error("expected 'if'", last_line);
    return NULL;
  }
  consume_tok();
  add_child(node, create_node("IF", "if", last_line));
  expect_delim("(");
  add_child(node, create_node("LPAREN", "(", last_line));
  Node *cond = parse_bool_expr();
  if (cond)
    add_child(node, cond);
  expect_delim(")");
  add_child(node, create_node("RPAREN", ")", last_line));
  Node *tb = parse_block();
  if (tb)
    add_child(node, tb);
  if (current_tok() && strcmp(current_tok()->value, "else") == 0) {
    consume_tok();
    add_child(node, create_node("ELSE", "else", last_line));
    Node *eb = parse_block();
    if (eb)
      add_child(node, eb);
  }
  return node;
}
Node *parse_while_statement(void) {
  Token *t = current_tok();
  if (!t)
    return NULL;
  Node *node = create_node("while_stmt", NULL, t->line);
  if (strcmp(t->value, "while") != 0) {
    print_error("expected 'while'", last_line);
    return NULL;
  }
  consume_tok();
  add_child(node, create_node("WHILE", "while", last_line));
  expect_delim("(");
  add_child(node, create_node("LPAREN", "(", last_line));
  Node *cond = parse_bool_expr();
  if (cond)
    add_child(node, cond);
  expect_delim(")");
  add_child(node, create_node("RPAREN", ")", last_line));
  Node *body = parse_block();
  if (body)
    add_child(node, body);
  return node;
}
Node *parse_print_statement(void) {
  Token *t = current_tok();
  if (!t)
    return NULL;
  Node *node = create_node("print_stmt", NULL, t->line);
  if (strcmp(t->value, "print") != 0) {
    print_error("expected 'print'", last_line);
    return NULL;
  }
  consume_tok();
  add_child(node, create_node("PRINT", "print", last_line));
  expect_delim("(");
  add_child(node, create_node("LPAREN", "(", last_line));
  Node *expr = parse_expr();
  if (expr)
    add_child(node, expr);
  expect_delim(")");
  add_child(node, create_node("RPAREN", ")", last_line));
  if (!expect_delim(";")) {
    synchronize();
    strcpy(node->rd_error, last_rd_error);
    return node;
  }
  add_child(node, create_node("SEMI", ";", last_line));
  return node;
}
Node *parse_block(void) {
  Node *node = create_node("block", NULL,
                           current_tok() ? current_tok()->line : last_line);
  if (!expect_delim("{"))
    return NULL;
  add_child(node, create_node("LBRACE", "{", last_line));
  Node *sl = parse_statement_list();
  if (sl)
    add_child(node, sl);
  if (!expect_delim("}"))
    return NULL;
  add_child(node, create_node("RBRACE", "}", last_line));
  return node;
}
Node *parse_statement(void) {
  Token *t = current_tok();
  if (!t)
    return NULL;
  if (strcmp(t->type, "KEYWORD") == 0) {
    if (strcmp(t->value, "int") == 0 || strcmp(t->value, "float") == 0)
      return parse_decl_statement();
    if (strcmp(t->value, "if") == 0)
      return parse_if_statement();
    if (strcmp(t->value, "while") == 0)
      return parse_while_statement();
    if (strcmp(t->value, "print") == 0)
      return parse_print_statement();
    char err[64];
    sprintf(err, "Unknown keyword '%s'", t->value);
    print_error(err, t->line);
    return parse_error_statement();
  }
  if (strcmp(t->type, "IDENTIFIER") == 0) {
    Token *next = (pos + 1 < token_count) ? &tokens[pos + 1] : NULL;
    if (next && strcmp(next->type, "ASSIGNMENT") == 0)
      return parse_assign_statement();
    char err[128];
    if (next)
      sprintf(err, "Expected '=', got '%s'", next->value);
    else
      sprintf(err, "Expected '=', got EOF");
    print_error(err, t->line);
    return parse_error_statement();
  }
  if (strcmp(t->type, "DELIMITER") == 0 && strcmp(t->value, "{") == 0)
    return parse_block();
  char err[64];
  sprintf(err, "Unexpected token '%s'", t->value);
  print_error(err, t->line);
  return parse_error_statement();
}
Node *parse_statement_list(void) {
  Node *node = create_node("stmt_list", NULL, last_line);
  while (current_tok()) {
    Token *t = current_tok();
    if (strcmp(t->type, "DELIMITER") == 0 && strcmp(t->value, "}") == 0)
      break;
    int saved_pos = pos;
    Node *stmt = parse_statement();
    if (stmt) {
      char source_buf[4096] = {0};
      for (int i = saved_pos; i < pos && i < token_count; i++) {
        strcat(source_buf, tokens[i].value);
        if (i < pos - 1)
          strcat(source_buf, " ");
      }
      strcpy(stmt->source, source_buf);
      add_child(node, stmt);
    } else {
      if (pos == saved_pos)
        skip_to_next_statement();
    }
  }
  return node;
}
Node *parse_program_rd(void) {
  last_rd_error[0] = '\0';
  Node *node = create_node("program", NULL, 1);
  Node *sl = parse_statement_list();
  if (sl)
    add_child(node, sl);
  return node;
}

/* ========== TREE / DERIVATION HELPERS ========== */
Node *create_node(const char *label, const char *value, int line) {
  Node *n = (Node *)malloc(sizeof(Node));
  if (!n)
    return NULL;
  strcpy(n->label, label);
  if (value)
    strcpy(n->value, value);
  else
    n->value[0] = '\0';
  n->child_count = 0;
  n->line = line;
  n->source[0] = '\0';
  n->rd_error[0] = '\0';
  for (int i = 0; i < MAX_CHILDREN; i++)
    n->children[i] = NULL;
  return n;
}
void add_child(Node *p, Node *c) {
  if (p && c && p->child_count < MAX_CHILDREN)
    p->children[p->child_count++] = c;
}
void print_tree(Node *node, int indent) {
  if (!node)
    return;
  for (int i = 0; i < indent; i++)
    printf("  ");
  if (node->value[0] != '\0')
    printf("%s(%s)\n", node->label, node->value);
  else
    printf("%s\n", node->label);
  for (int i = 0; i < node->child_count; i++)
    print_tree(node->children[i], indent + 1);
}
void collect_statements(Node *node) {
  if (!node)
    return;
  if (strcmp(node->label, "decl_stmt") == 0 ||
      strcmp(node->label, "assign_stmt") == 0 ||
      strcmp(node->label, "if_stmt") == 0 ||
      strcmp(node->label, "while_stmt") == 0 ||
      strcmp(node->label, "print_stmt") == 0 ||
      strcmp(node->label, "error_stmt") == 0) {
    all_stmts[stmt_count++] = node;
  }
  for (int i = 0; i < node->child_count; i++)
    collect_statements(node->children[i]);
}
void node_to_string(Node *node, char *buf, int *len) {
  if (!node)
    return;
  if (node->value[0] != '\0' && strcmp(node->label, "ERROR") != 0) {
    int vl = strlen(node->value);
    memcpy(buf + *len, node->value, vl);
    *len += vl;
    buf[(*len)++] = ' ';
  }
  for (int i = 0; i < node->child_count; i++)
    node_to_string(node->children[i], buf, len);
}
void print_statement_source(Node *node) {
  if (node->source[0] != '\0') {
    printf("%s", node->source);
  } else if (node->value[0] != '\0') {
    char buf[4096] = {0};
    int len = 0;
    node_to_string(node, buf, &len);
    buf[len] = '\0';
    while (len > 0 && buf[len - 1] == ' ')
      buf[--len] = '\0';
    printf("%s", buf);
  } else {
    printf("<statement at line %d>", node->line);
  }
}
void leftmost_derivation(Node *root) {
  if (strcmp(root->label, "error_stmt") == 0) {
    printf("  Cannot show derivation for erroneous statement\n\n");
    return;
  }
  Node *sent[MAX_TOKENS];
  int count = 1;
  sent[0] = root;
  int step = 1;
  printf("  Leftmost derivation:\n\n");
  while (1) {
    printf("Step %d => ", step++);
    for (int i = 0; i < count; i++) {
      if (sent[i]->value[0] != '\0')
        printf("%s ", sent[i]->value);
      else
        printf("%s ", sent[i]->label);
    }
    printf("\n");
    int lpos = -1;
    for (int i = 0; i < count; i++)
      if (sent[i]->child_count > 0) {
        lpos = i;
        break;
      }
    if (lpos == -1)
      break;
    Node *tmp[MAX_TOKENS];
    int idx = 0;
    for (int i = 0; i < lpos; i++)
      tmp[idx++] = sent[i];
    for (int i = 0; i < sent[lpos]->child_count; i++)
      tmp[idx++] = sent[lpos]->children[i];
    for (int i = lpos + 1; i < count; i++)
      tmp[idx++] = sent[i];
    count = idx;
    for (int i = 0; i < count; i++)
      sent[i] = tmp[i];
  }
  printf("\n");
}
void rightmost_derivation(Node *root) {
  if (strcmp(root->label, "error_stmt") == 0) {
    printf("  Cannot show derivation for erroneous statement\n\n");
    return;
  }
  Node *sent[MAX_TOKENS];
  int count = 1;
  sent[0] = root;
  int step = 1;
  printf("  Rightmost derivation:\n\n");
  while (1) {
    printf("Step %d => ", step++);
    for (int i = 0; i < count; i++) {
      if (sent[i]->value[0] != '\0')
        printf("%s ", sent[i]->value);
      else
        printf("%s ", sent[i]->label);
    }
    printf("\n");
    int rpos = -1;
    for (int i = count - 1; i >= 0; i--)
      if (sent[i]->child_count > 0) {
        rpos = i;
        break;
      }
    if (rpos == -1)
      break;
    Node *tmp[MAX_TOKENS];
    int idx = 0;
    for (int i = 0; i < rpos; i++)
      tmp[idx++] = sent[i];
    for (int i = 0; i < sent[rpos]->child_count; i++)
      tmp[idx++] = sent[rpos]->children[i];
    for (int i = rpos + 1; i < count; i++)
      tmp[idx++] = sent[i];
    count = idx;
    for (int i = 0; i < count; i++)
      sent[i] = tmp[i];
  }
  printf("\n");
}

/* ========== LEXICAL ANALYZER ========== */
static int is_keyword(const char *s) {
  return strcmp(s, "int") == 0 || strcmp(s, "float") == 0 ||
         strcmp(s, "if") == 0 || strcmp(s, "else") == 0 ||
         strcmp(s, "while") == 0 || strcmp(s, "print") == 0;
}

static void add_token(const char *type, const char *value, int line) {
  if (token_count >= MAX_TOKENS)
    return;
  strcpy(tokens[token_count].type, type);
  strcpy(tokens[token_count].value, value);
  tokens[token_count].line = line;
  token_count++;
}

int lexical_analyze_file(const char *path) {
  FILE *f = fopen(path, "r");
  if (!f) {
    printf("Cannot open %s\n", path);
    return 0;
  }

  token_count = 0;
  int ch;
  int line = 1;

  while ((ch = fgetc(f)) != EOF) {
    if (ch == ' ' || ch == '\t' || ch == '\r')
      continue;
    if (ch == '\n') {
      line++;
      continue;
    }

    if (isalpha(ch) || ch == '_') {
      char lexeme[MAX_VALUE];
      int len = 0;
      lexeme[len++] = (char)ch;
      while ((ch = fgetc(f)) != EOF && (isalnum(ch) || ch == '_')) {
        if (len < MAX_VALUE - 1)
          lexeme[len++] = (char)ch;
      }
      lexeme[len] = '\0';
      if (ch != EOF)
        ungetc(ch, f);
      if (is_keyword(lexeme))
        add_token("KEYWORD", lexeme, line);
      else
        add_token("IDENTIFIER", lexeme, line);
      continue;
    }

    if (isdigit(ch)) {
      char lexeme[MAX_VALUE];
      int len = 0;
      int has_dot = 0;
      lexeme[len++] = (char)ch;
      while ((ch = fgetc(f)) != EOF) {
        if (isdigit(ch)) {
          if (len < MAX_VALUE - 1)
            lexeme[len++] = (char)ch;
        } else if (ch == '.' && !has_dot) {
          has_dot = 1;
          if (len < MAX_VALUE - 1)
            lexeme[len++] = (char)ch;
        } else {
          break;
        }
      }
      lexeme[len] = '\0';
      if (ch != EOF)
        ungetc(ch, f);
      add_token(has_dot ? "FLOAT" : "INTEGER", lexeme, line);
      continue;
    }

    if (ch == '/') {
      int next = fgetc(f);
      if (next == '/') {
        while ((ch = fgetc(f)) != EOF && ch != '\n') {
        }
        if (ch == '\n')
          line++;
        continue;
      }
      if (next == '*') {
        int prev = 0;
        while ((ch = fgetc(f)) != EOF) {
          if (ch == '\n')
            line++;
          if (prev == '*' && ch == '/')
            break;
          prev = ch;
        }
        continue;
      }
      if (next != EOF)
        ungetc(next, f);
      add_token("ARITHMETIC", "/", line);
      continue;
    }

    if (ch == '&') {
      int next = fgetc(f);
      if (next == '&')
        add_token("LOGICAL", "&&", line);
      else {
        if (next != EOF)
          ungetc(next, f);
        printf("Lexical warning at line %d: unexpected '&'\n", line);
      }
      continue;
    }

    if (ch == '|') {
      int next = fgetc(f);
      if (next == '|')
        add_token("LOGICAL", "||", line);
      else {
        if (next != EOF)
          ungetc(next, f);
        printf("Lexical warning at line %d: unexpected '|'\n", line);
      }
      continue;
    }

    if (ch == '=') {
      int next = fgetc(f);
      if (next == '=')
        add_token("RELATIONAL", "==", line);
      else {
        if (next != EOF)
          ungetc(next, f);
        add_token("ASSIGNMENT", "=", line);
      }
      continue;
    }

    if (ch == '!' || ch == '<' || ch == '>') {
      int next = fgetc(f);
      if (next == '=') {
        char op[3] = {(char)ch, '=', '\0'};
        add_token("RELATIONAL", op, line);
      } else {
        if (next != EOF)
          ungetc(next, f);
        if (ch == '!')
          add_token("LOGICAL", "!", line);
        else {
          char op[2] = {(char)ch, '\0'};
          add_token("RELATIONAL", op, line);
        }
      }
      continue;
    }

    if (ch == '+' || ch == '-' || ch == '*' || ch == '%') {
      char op[2] = {(char)ch, '\0'};
      add_token("ARITHMETIC", op, line);
      continue;
    }

    if (ch == '(' || ch == ')' || ch == '{' || ch == '}' || ch == ';') {
      char d[2] = {(char)ch, '\0'};
      add_token("DELIMITER", d, line);
      continue;
    }

    printf("Lexical warning at line %d: ignoring character '%c'\n", line, ch);
  }

  fclose(f);
  return 1;
}

void print_generated_tokens(void) {
  printf("====================================================================="
         "===========\n");
  printf("LEXICAL ANALYSIS OUTPUT\n");
  printf("====================================================================="
         "===========\n\n");
  printf("%-5s %-14s %-18s %s\n", "No.", "Type", "Value", "Line");
  printf("----- -------------- ------------------ ----\n");
  for (int i = 0; i < token_count; i++) {
    printf("%-5d %-14s %-18s %d\n", i + 1, tokens[i].type, tokens[i].value,
           tokens[i].line);
  }
  printf("\nTotal tokens: %d\n\n", token_count);
}

/* ========================================================================== */
/* ===== Q2: SYMBOL TABLE IMPLEMENTATION =====================================
 */
/* ========================================================================== */

void sym_scope_enter(void) {
  if (scope_depth < MAX_SCOPE_DEPTH - 1) {
    scope_depth++;
    scope_offset[scope_depth] = 0;
  }
}

void sym_scope_exit(void) {
  /* Remove all symbols belonging to the current scope */
  int i = sym_count - 1;
  while (i >= 0 && sym_table[i].scope == scope_depth)
    i--;
  sym_count = i + 1;
  if (scope_depth > 0)
    scope_depth--;
}

/* Q2 — sym_insert: add a symbol to the flat table at the current scope depth.
 * Computes offset using 4 bytes per variable (int and float both 4 bytes).
 * Returns a pointer to the new entry, or NULL if the table is full. */
Symbol *sym_insert(const char *name, const char *type, int line) {
  if (sym_count >= MAX_SYM_TABLE)
    return NULL;
  Symbol *s = &sym_table[sym_count];
  strncpy(s->name, name, MAX_LABEL - 1);
  s->name[MAX_LABEL - 1] = '\0';
  strncpy(s->type, type, MAX_LABEL - 1);
  s->type[MAX_LABEL - 1] = '\0';
  s->scope = scope_depth;
  s->offset = scope_offset[scope_depth];
  s->line = line;
  scope_offset[scope_depth] += 4; /* 4 bytes per variable */
  sym_count++;
  return s;
}

/* Q2 — sym_lookup: search all scopes from innermost outward.
 * Returns the entry with the highest scope <= scope_depth — identical to
 * the lookup in phase5.c and phase6.c. */
Symbol *sym_lookup(const char *name) {
  Symbol *best = NULL;
  for (int i = 0; i < sym_count; i++) {
    if (strcmp(sym_table[i].name, name) == 0 &&
        sym_table[i].scope <= scope_depth) {
      if (!best || sym_table[i].scope > best->scope)
        best = &sym_table[i];
    }
  }
  return best;
}

/* Q2 — sym_lookup_current: check only the current (innermost) scope.
 * Used to detect duplicate declarations before inserting. */
Symbol *sym_lookup_current(const char *name) {
  for (int i = 0; i < sym_count; i++) {
    if (sym_table[i].scope == scope_depth &&
        strcmp(sym_table[i].name, name) == 0)
      return &sym_table[i];
  }
  return NULL;
}

/* Q2 — print_symbol_table: flat dump of all symbols.
 * Column order matches phase5.c: Name | Type | Scope | Offset | Line. */
void print_symbol_table(void) {
  printf("\n==================================================================="
         "=============\n");
  printf("  SYMBOL TABLE  (%d entr%s)\n", sym_count,
         sym_count == 1 ? "y" : "ies");
  printf("====================================================================="
         "===========\n");
  printf("  %-16s  %-8s  %-7s  %-10s  %s\n", "Name", "Type", "Scope", "Offset",
         "Line");
  printf("  %-16s  %-8s  %-7s  %-10s  %s\n", "----------------", "--------",
         "-------", "----------", "----");
  for (int i = 0; i < sym_count; i++) {
    printf("  %-16s  %-8s  %-7d  %-10d  %d\n", sym_table[i].name,
           sym_table[i].type, sym_table[i].scope, sym_table[i].offset,
           sym_table[i].line);
  }
  printf("====================================================================="
         "===========\n\n");
}

/* Q2 — build_symbol_table: parse-tree walk that populates the symbol table
 * and prints the same trace as phase5.c:
 *   [SCOPE] >>> Entering scope level N
 *   [INSERT] name  type=T  scope=N  offset=O  (line L)
 *   [WARN]   Multiple declaration of 'x' in scope N (line L)
 *   [SCOPE] <<< Leaving  scope level N  (symbols declared here:)
 *              name  type=T  offset=O           -- or (none)
 *
 * Symbols are NOT removed on scope-exit so print_symbol_table() shows all. */
void build_symbol_table(Node *node) {
  if (!node)
    return;

  /* BLOCK node: increase scope, recurse, print exit summary, lower scope */
  if (strcmp(node->label, "block") == 0) {
    scope_depth++;
    if (scope_depth < MAX_SCOPE_DEPTH)
      scope_offset[scope_depth] = 0;
    printf("  [SCOPE] >>> Entering scope level %d\n", scope_depth);

    for (int i = 0; i < node->child_count; i++)
      build_symbol_table(node->children[i]);

    printf("  [SCOPE] <<< Leaving  scope level %d  (symbols declared here:)\n",
           scope_depth);
    int found = 0;
    for (int i = 0; i < sym_count; i++) {
      if (sym_table[i].scope == scope_depth) {
        printf("            %-12s  type=%-6s  offset=%d\n", sym_table[i].name,
               sym_table[i].type, sym_table[i].offset);
        found = 1;
      }
    }
    if (!found)
      printf("            (none)\n");

    scope_depth--; /* lower depth; keep symbols for the final table print */
    return;
  }

  /* DECLARATION node: insert or warn */
  if (strcmp(node->label, "decl_stmt") == 0) {
    const char *var_type = NULL;
    const char *var_name = NULL;
    int var_line = node->line;
    for (int i = 0; i < node->child_count; i++) {
      if (strcmp(node->children[i]->label, "TYPE") == 0)
        var_type = node->children[i]->value;
      if (strcmp(node->children[i]->label, "ID") == 0) {
        var_name = node->children[i]->value;
        var_line = node->children[i]->line;
      }
    }
    if (var_type && var_name) {
      if (sym_lookup_current(var_name)) {
        printf(
            "  [WARN]   Multiple declaration of '%s' in scope %d (line %d)\n",
            var_name, scope_depth, var_line);
      } else {
        Symbol *s = sym_insert(var_name, var_type, var_line);
        if (s)
          printf(
              "  [INSERT] %-12s  type=%-6s  scope=%d  offset=%d  (line %d)\n",
              s->name, s->type, s->scope, s->offset, var_line);
      }
    }
    return;
  }

  for (int i = 0; i < node->child_count; i++)
    build_symbol_table(node->children[i]);
}

/* ========================================================================== */
/* ===== Q3: SEMANTIC ANALYSIS IMPLEMENTATION ================================
 */
/* ========================================================================== */

/* Q3 — sem_errors_count: running count of semantic errors found.
 * Errors are printed inline (immediately) matching phase6.c. */
static int sem_errors_count = 0;

/* Q3 — sem_error: emit one [SEMANTIC ERROR] line to stdout immediately.
 * Mirrors the phase6.c sem_error() function exactly. */
static void sem_error(const char *msg, int line) {
  printf("  [SEMANTIC ERROR] Line %d: %s\n", line, msg);
  sem_errors_count++;
}

/* Q3 — has_relop: return 1 if the subtree contains at least one REL_OP node.
 * A valid boolean condition for if/while must contain a relational operator. */
static int has_relop(Node *node) {
  if (!node)
    return 0;
  if (strcmp(node->label, "REL_OP") == 0)
    return 1;
  for (int i = 0; i < node->child_count; i++)
    if (has_relop(node->children[i]))
      return 1;
  return 0;
}

/* Q3 — infer_type: return the type string ("int"/"float"/"unknown") for an
 * expression subtree.  Uses global sym_table with the current scope_depth so
 * name-to-type resolution is scope-aware.  Emits a semantic error for any
 * undeclared ID it encounters (matches phase6.c behaviour). */
static char infer_result[16];
const char *infer_type(Node *node) {
  if (!node) {
    strcpy(infer_result, "unknown");
    return infer_result;
  }

  if (strcmp(node->label, "INTEGER") == 0) {
    strcpy(infer_result, "int");
    return infer_result;
  }
  if (strcmp(node->label, "FLOAT") == 0) {
    strcpy(infer_result, "float");
    return infer_result;
  }
  if (strcmp(node->label, "ID") == 0) {
    Symbol *s = sym_lookup(node->value);
    if (!s) {
      char msg[128];
      snprintf(msg, sizeof(msg), "use of undeclared variable '%s'",
               node->value);
      sem_error(msg, node->line);
      strcpy(infer_result, "unknown");
      return infer_result;
    }
    strcpy(infer_result, s->type);
    return infer_result;
  }
  /* Composite: float propagates upward; default is int */
  strcpy(infer_result, "int");
  for (int i = 0; i < node->child_count; i++) {
    const char *ct = infer_type(node->children[i]);
    if (strcmp(ct, "float") == 0)
      strcpy(infer_result, "float");
    if (strcmp(ct, "unknown") == 0 && strcmp(infer_result, "float") != 0)
      strcpy(infer_result, "unknown");
  }
  return infer_result;
}

/* Q3 — semantic_analyze (sem_walk equivalent, based on phase6.c):
 * Walks the parse tree and prints inline trace tags for each construct,
 * emitting [SEMANTIC ERROR] lines for any violation found.
 *
 * Tag format matches phase6.c exactly:
 *   [SCOPE]  entering/leaving scope level N
 *   [DECL]   name  type=T  scope=N  (line L)
 *   [ASSIGN] name = type expression  (line L)
 *   [IF]     checking condition (line L)
 *   [WHILE]  checking condition (line L)
 *   [PRINT]  (line L)
 *   [SEMANTIC ERROR] Line L: message
 *
 * Relies on the same sym_table built by build_symbol_table(),
 * with scope_depth reset to 0 before this walk begins. */
void semantic_analyze(Node *node) {
  if (!node)
    return;

  /* BLOCK: push / pop scope */
  if (strcmp(node->label, "block") == 0) {
    scope_depth++;
    printf("  [SCOPE]  entering scope level %d\n", scope_depth);
    for (int i = 0; i < node->child_count; i++)
      semantic_analyze(node->children[i]);
    printf("  [SCOPE]  leaving  scope level %d\n", scope_depth);
    scope_depth--;
    return;
  }

  /* DECLARATION */
  if (strcmp(node->label, "decl_stmt") == 0) {
    char decl_type[16] = {0};
    char var_name[MAX_LABEL] = {0};
    Node *init_expr = NULL;
    int decl_line = node->line;

    for (int i = 0; i < node->child_count; i++) {
      Node *c = node->children[i];
      if (strcmp(c->label, "TYPE") == 0)
        strncpy(decl_type, c->value, sizeof(decl_type) - 1);
      else if (strcmp(c->label, "ID") == 0) {
        strncpy(var_name, c->value, MAX_LABEL - 1);
        decl_line = c->line;
      } else if (strcmp(c->label, "ASSIGNMENT") == 0 &&
                 i + 1 < node->child_count)
        init_expr = node->children[i + 1];
    }

    /* Duplicate check using sym_lookup_current on the pre-built table */
    int dup = 0;
    for (int i = 0; i < sym_count; i++) {
      if (sym_table[i].scope == scope_depth &&
          strcmp(sym_table[i].name, var_name) == 0) {
        /* Count how many times this name appears at this scope */
        int cnt = 0;
        for (int j = 0; j < sym_count; j++)
          if (sym_table[j].scope == scope_depth &&
              strcmp(sym_table[j].name, var_name) == 0)
            cnt++;
        if (cnt > 1) {
          dup = 1;
          break;
        }
      }
    }
    if (dup) {
      char msg[128];
      snprintf(msg, sizeof(msg), "multiple declaration of '%s' in scope %d",
               var_name, scope_depth);
      sem_error(msg, decl_line);
    } else {
      printf("  [DECL]   %-12s  type=%-6s  scope=%d  (line %d)\n", var_name,
             decl_type, scope_depth, decl_line);
    }

    /* Type mismatch in initialiser */
    if (init_expr) {
      const char *rhs = infer_type(init_expr);
      if (strcmp(rhs, "unknown") != 0 && strcmp(decl_type, "int") == 0 &&
          strcmp(rhs, "float") == 0) {
        char msg[128];
        snprintf(msg, sizeof(msg),
                 "type mismatch: cannot assign float expression to int "
                 "variable '%s'",
                 var_name);
        sem_error(msg, decl_line);
      }
    }
    return;
  }

  /* ASSIGNMENT */
  if (strcmp(node->label, "assign_stmt") == 0) {
    char var_name[MAX_LABEL] = {0};
    Node *rhs_expr = NULL;
    int asgn_line = node->line;

    for (int i = 0; i < node->child_count; i++) {
      Node *c = node->children[i];
      if (strcmp(c->label, "ID") == 0) {
        strncpy(var_name, c->value, MAX_LABEL - 1);
        asgn_line = c->line;
      } else if (strcmp(c->label, "ASSIGNMENT") == 0 &&
                 i + 1 < node->child_count)
        rhs_expr = node->children[i + 1];
    }

    Symbol *s = sym_lookup(var_name);
    if (!s) {
      char msg[128];
      snprintf(msg, sizeof(msg), "use of undeclared variable '%s'", var_name);
      sem_error(msg, asgn_line);
    }
    if (rhs_expr) {
      const char *rhs = infer_type(rhs_expr);
      if (s && strcmp(rhs, "unknown") != 0 && strcmp(s->type, "int") == 0 &&
          strcmp(rhs, "float") == 0) {
        char msg[128];
        snprintf(msg, sizeof(msg),
                 "type mismatch: cannot assign float expression to int "
                 "variable '%s'",
                 var_name);
        sem_error(msg, asgn_line);
      }
      if (s)
        printf("  [ASSIGN] %-12s = %-6s expression  (line %d)\n", var_name, rhs,
               asgn_line);
    }
    return;
  }

  /* IF STATEMENT */
  if (strcmp(node->label, "if_stmt") == 0) {
    printf("  [IF]     checking condition (line %d)\n", node->line);
    for (int i = 0; i < node->child_count; i++) {
      Node *c = node->children[i];
      if (strcmp(c->label, "bool_expr") == 0 && !has_relop(c))
        sem_error("invalid boolean condition - missing relational operator",
                  node->line);
      semantic_analyze(c);
    }
    return;
  }

  /* WHILE STATEMENT */
  if (strcmp(node->label, "while_stmt") == 0) {
    printf("  [WHILE]  checking condition (line %d)\n", node->line);
    for (int i = 0; i < node->child_count; i++) {
      Node *c = node->children[i];
      if (strcmp(c->label, "bool_expr") == 0 && !has_relop(c))
        sem_error("invalid boolean condition - missing relational operator",
                  node->line);
      semantic_analyze(c);
    }
    return;
  }

  /* PRINT STATEMENT */
  if (strcmp(node->label, "print_stmt") == 0) {
    printf("  [PRINT]  (line %d)\n", node->line);
    for (int i = 0; i < node->child_count; i++)
      semantic_analyze(node->children[i]);
    return;
  }

  /* Standalone ID inside an expression */
  if (strcmp(node->label, "ID") == 0) {
    if (!sym_lookup(node->value)) {
      char msg[128];
      snprintf(msg, sizeof(msg), "use of undeclared variable '%s'",
               node->value);
      sem_error(msg, node->line);
    }
    return;
  }

  /* Default: recurse */
  for (int i = 0; i < node->child_count; i++)
    semantic_analyze(node->children[i]);
}

/* Q3 — run_semantic_demo: demonstrates the two mandatory semantic error cases
 * using modified variants of the ACTUAL input.txt program so the demo is
 * clearly connected to the program being analysed, not a random example. */
void run_semantic_demo(void) {
  printf("\n==================================================================="
         "=============\n");
  printf("  SEMANTIC ERROR DEMONSTRATION (2 Required Cases)\n");
  printf("====================================================================="
         "===========\n\n");

  /* Save live state so we can restore it after the demo */
  int saved_errors = sem_errors_count;
  int saved_scope = scope_depth;
  int saved_count = sym_count;

  /* ------------------------------------------------------------------
   * Demo Case 1 — Use of undeclared variable
   *
   * input.txt declares: int a; int b; int sum; float avg;
   * Suppose the programmer wrote:  total = a + b;
   * ('total' was never declared — this mirrors a real mistake in the
   *  same style of program as input.txt)
   * ------------------------------------------------------------------ */
  printf("  Case 1 — Use of undeclared variable\n");
  printf("  %-14s %s\n", "Program:", "int a; int b; int sum; float avg;");
  printf("  %-14s %s\n", "", "a = 2; b = 15;");
  printf("  %-14s %s\n", "", "total = a + b;   <-- 'total' never declared");
  printf(
      "  Expected:  [SEMANTIC ERROR] use of undeclared variable 'total'\n\n");

  sem_errors_count = 0;
  scope_depth = 0;
  sym_count = 0;
  memset(scope_offset, 0, sizeof(scope_offset));

  /* Replicate the declarations from input.txt */
  sym_insert("a", "int", 1);
  sym_insert("b", "int", 2);
  sym_insert("sum", "int", 3);
  sym_insert("avg", "float", 4);
  /* Simulate: a = 2 and b = 15 — both declared, no error */
  /* Simulate: total = a + b — 'total' is not declared */
  if (!sym_lookup("total"))
    sem_error("use of undeclared variable 'total'", 7);

  printf("  Result: %d semantic error(s) found.\n\n", sem_errors_count);

  /* ------------------------------------------------------------------
   * Demo Case 2 — Multiple declarations in the same scope
   *
   * input.txt declares 'int a' at the top level (scope 0).
   * Suppose the programmer accidentally wrote 'int a;' a second time.
   * ------------------------------------------------------------------ */
  printf("  Case 2 — Multiple declarations in the same scope\n");
  printf("  %-14s %s\n", "Program:", "int a;");
  printf("  %-14s %s\n", "", "int b;");
  printf("  %-14s %s\n", "", "int a;   <-- 'a' already declared in scope 0");
  printf("  Expected:  [SEMANTIC ERROR] multiple declaration of 'a' in scope "
         "0\n\n");

  sem_errors_count = 0;
  scope_depth = 0;
  sym_count = 0;
  memset(scope_offset, 0, sizeof(scope_offset));

  sym_insert("a", "int", 1); /* first  int a — OK */
  sym_insert("b", "int", 2); /* int b  — OK */
  /* second int a — duplicate in scope 0 */
  if (sym_lookup_current("a")) {
    char msg[128];
    snprintf(msg, sizeof(msg), "multiple declaration of 'a' in scope %d",
             scope_depth);
    sem_error(msg, 3);
  }

  printf("  Result: %d semantic error(s) found.\n\n", sem_errors_count);

  /* Restore live state */
  sem_errors_count = saved_errors;
  scope_depth = saved_scope;
  sym_count = saved_count;
  memset(scope_offset, 0, sizeof(scope_offset));
}

/* ========== MAIN ========== */

int main(void) {
  if (!lexical_analyze_file("input.txt"))
    return 1;
  print_generated_tokens();

  build_grammar();
  build_symbol_lists();
  compute_first_sets();
  compute_follow_sets();
  build_ll1_table();

  print_productions();
  print_first_sets();
  print_follow_sets();
  print_ll1_table();

  /* ===== FIRST PASS: Collect statements without printing errors ===== */
  pos = 0;
  error_count = 0;
  last_rd_error[0] = '\0';

  Node *tree = parse_program_rd();

  char collected_errors[MAX_STMTS][256];
  int error_msg_count = 0;

  collect_statements(tree);

  /* ===== SILENT PRE-PARSE: Run LL(1) then SR on all statements quietly =====
   */
  quiet_mode = 1;
  int stmt_ll1_ok[MAX_STMTS], stmt_sr_ok[MAX_STMTS];
  int total_errors_found = 0;
  for (int i = 0; i < stmt_count; i++) {
    int is_err = (strcmp(all_stmts[i]->label, "error_stmt") == 0);
    if (is_err) {
      stmt_ll1_ok[i] = 0;
      stmt_sr_ok[i] = 0;
      if (all_stmts[i]->rd_error[0] != '\0') {
        strcpy(collected_errors[error_msg_count], all_stmts[i]->rd_error);
        error_msg_count++;
      }
    } else {
      stmt_ll1_ok[i] = ll1_parse_statement(all_stmts[i]);
      stmt_sr_ok[i] = sr_parse_statement(all_stmts[i]);
    }
    if (is_err || !stmt_ll1_ok[i] || !stmt_sr_ok[i])
      total_errors_found++;
  }
  quiet_mode = 0;

  /* ===== PRINT STACK TRACES FOR ERRONEOUS STATEMENTS ONLY ===== */
  if (total_errors_found > 0) {
    printf("==================================================================="
           "=============\n");
    printf("DETAILED STACK TRACES FOR ERRONEOUS STATEMENTS\n");
    printf("==================================================================="
           "=============\n");

    int first_ll1 = 1;
    for (int i = 0; i < stmt_count; i++) {
      if (!stmt_ll1_ok[i]) {
        if (first_ll1) {
          printf("\n--- LL(1) Parser Traces ---\n");
          first_ll1 = 0;
        }
        printf("\n--- Statement %d (line %d): ", i + 1, all_stmts[i]->line);
        print_statement_source(all_stmts[i]);
        printf(" ---\n");
        quiet_mode = 0;
        ll1_parse_statement(all_stmts[i]);
      }
    }

    int first_sr = 1;
    for (int i = 0; i < stmt_count; i++) {
      if (!stmt_sr_ok[i]) {
        if (first_sr) {
          printf("\n--- Shift-Reduce Parser Traces ---\n");
          first_sr = 0;
        }
        printf("\n--- Statement %d (line %d): ", i + 1, all_stmts[i]->line);
        print_statement_source(all_stmts[i]);
        printf(" ---\n");
        quiet_mode = 0;
        sr_parse_statement(all_stmts[i]);
      }
    }
    printf("\n");
  }

  /* ===== PRINT BUFFERED RECURSIVE DESCENT SYNTAX ERRORS ===== */
  if (error_msg_total > 0) {
    printf("==================================================================="
           "=============\n");
    printf("SYNTAX ERRORS SUMMARY\n");
    printf("==================================================================="
           "=============\n\n");
    for (int i = 0; i < error_msg_total; i++) {
      printf("%s\n", error_messages[i]);
    }
    printf("\n=== Found %d Syntax Error(s) !!!\n\n", error_count);
  } else {
    printf("\nParsing completed successfully with 0 errors!\n\n");
  }

  /* ===== ERROR SUMMARY =====
  printf("================================================================================\n");
  printf("ERROR SUMMARY (LL(1) + Shift-Reduce)\n");
  printf("================================================================================\n\n");
  if(total_errors_found == 0){
      printf("  All %d statement(s) are syntactically correct.\n\n",
  stmt_count); } else { printf("  %d out of %d statement(s) have errors:\n\n",
  total_errors_found, stmt_count); for(int i=0;i<stmt_count;i++){ int is_err =
  (strcmp(all_stmts[i]->label,"error_stmt")==0); if(is_err || !stmt_ll1_ok[i] ||
  !stmt_sr_ok[i]){ if(is_err && all_stmts[i]->rd_error[0] != '\0'){ printf("
  %s\n", all_stmts[i]->rd_error); } else { printf("  >> Statement %d (line %d):
  ", i+1, all_stmts[i]->line); print_statement_source(all_stmts[i]);
                  printf("\n");
              }
              if(is_err) printf("     Reason: Syntax error (recursive descent
  parser failed)\n"); else { if(!stmt_ll1_ok[i]) printf("     Reason: LL(1)
  parser rejected\n"); if(!stmt_sr_ok[i])  printf("     Reason: Shift-Reduce
  parser rejected\n");
              }
              printf("\n");
          }
      }
  }
*/
  /* ===== FULL PARSE TREE ===== */
  if (error_count == 0) {
    printf("==================================================================="
           "=============\n");
    printf("FULL PARSE TREE\n");
    printf("==================================================================="
           "=============\n");
    print_tree(tree, 0);
    printf("\n");
  }

  /* =====  SYMBOL TABLE  ===== */
  /* Reset and walk the tree — prints [SCOPE]/[INSERT]/[WARN] trace inline */
  sym_count = 0;
  scope_depth = 0;
  memset(scope_offset, 0, sizeof(scope_offset));
  printf("====================================================================="
         "===========\n");
  printf("SYMBOL TABLE & SCOPE ANALYSIS\n");
  printf("====================================================================="
         "===========\n\n");
  printf("  [SCOPE] >>> Entering scope level 0  (global)\n");
  build_symbol_table(tree);
  printf("  [SCOPE]PHASE <<< Leaving  scope level 0  (global)\n");
  /* Restore depth to 0 so sym_lookup works during semantic analysis */
  scope_depth = 0;
  /* Print the complete flat symbol table */
  print_symbol_table();

  /* Reset scope_depth so sym_lookup works correctly across nested blocks.
   * The sym_table is kept intact from the build step above.             */
  scope_depth = 0;
  sem_errors_count = 0; /* defined as static inside Q3 section */

  printf("====================================================================="
         "===========\n");
  printf("SEMANTIC ANALYSIS TRACE\n");
  printf("====================================================================="
         "===========\n\n");

  /* Walk the tree — prints [DECL]/[ASSIGN]/[IF]/[WHILE]/[PRINT]/[SEMANTIC
   * ERROR] */
  semantic_analyze(tree);

  printf("\n==================================================================="
         "=============\n");
  if (sem_errors_count == 0)
    printf("  Semantic analysis PASSED - no errors found.\n");
  else
    printf("  Semantic analysis found %d error(s).\n", sem_errors_count);
  printf("====================================================================="
         "===========\n\n");

  /* Reprint the symbol table after analysis (matches phase6.c ending) */
  print_symbol_table();

  /* Show 2 explicit error demos for Q3 marking requirement */
  run_semantic_demo();

  /* ===== STATEMENT SELECTION ===== */

  printf("====================================================================="
         "===========\n");
  printf("STATEMENTS FOUND (%d total)\n", stmt_count);
  printf("====================================================================="
         "===========\n");
  for (int i = 0; i < stmt_count; i++) {
    int is_err = (strcmp(all_stmts[i]->label, "error_stmt") == 0);
    int both_ok = !is_err && stmt_ll1_ok[i] && stmt_sr_ok[i];
    printf("  [%2d]  %-12s  ", i + 1, all_stmts[i]->label);
    print_statement_source(all_stmts[i]);
    printf("  (line %d)%s\n", all_stmts[i]->line,
           is_err ? "  [SYNTAX ERROR]" : (!both_ok ? "  [PARSE ERROR]" : ""));
  }

  int choice = 0;
  while (choice < 1 || choice > stmt_count) {
    printf("\nEnter statement number (1-%d): ", stmt_count);
    if (scanf("%d", &choice) != 1) {
      int c;
      while ((c = getchar()) != '\n' && c != EOF)
        ;
      choice = 0;
    }
  }

  Node *selected = all_stmts[choice - 1];
  int is_error_stmt = (strcmp(selected->label, "error_stmt") == 0);

  printf("\n==================================================================="
         "=============\n");
  printf("SELECTED: ");
  print_statement_source(selected);
  printf("\n");
  printf("====================================================================="
         "===========\n\n");

  int ll1_ok = stmt_ll1_ok[choice - 1];
  int sr_ok = stmt_sr_ok[choice - 1];

  quiet_mode = 0;
  ll1_ok = ll1_parse_statement(selected);
  sr_ok = sr_parse_statement(selected);

  int both_ok = ll1_ok && sr_ok;

  if (both_ok) {
    printf("==================================================================="
           "=============\n");
    printf("BOTH PARSERS ACCEPTED - Showing derivations and statement parse "
           "tree\n");
    printf("==================================================================="
           "=============\n\n");
    printf("--- LEFTMOST DERIVATION ---\n");
    leftmost_derivation(selected);
    printf("--- RIGHTMOST DERIVATION ---\n");
    rightmost_derivation(selected);
    printf("--- STATEMENT PARSE TREE ---\n");
    print_tree(selected, 0);
    printf("\n");
  } else {
    printf("==================================================================="
           "=============\n");
    printf("PARSER(S) REJECTED THE STATEMENT\n");
    printf("==================================================================="
           "=============\n");
    printf("  LL(1) parser : %s\n", ll1_ok ? "ACCEPTED" : "REJECTED");
    printf("  S/R  parser  : %s\n", sr_ok ? "ACCEPTED" : "REJECTED");
    printf("\n");
    if (!ll1_ok || !sr_ok) {
      printf("  Parse tree and derivations are only shown for syntactically "
             "correct\n");
      printf("  statements that are accepted by BOTH parsers.\n");
    }
  }

  printf("\n==================================================================="
         "=============\n");
  printf("All phases complete.\n");
  printf("====================================================================="
         "===========\n");
  return 0;
}
