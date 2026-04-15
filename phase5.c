/*
 * ============================================================
 *  PHASE 5 - SYMBOL TABLE WITH SCOPE HANDLING
 *  Reads tokens.txt (from Phase 1) and the parse tree
 *  produced by Phase 4's recursive descent parser.
 *
 *  Stores  : variable name, type, scope level, memory offset
 *  Supports: insertion, lookup (current + outer scopes),
 *            nested block scopes (push / pop)
 * ============================================================
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

/* ===================== CONFIGURATION ===================== */
#define MAX_TOKENS      2000
#define MAX_CHILDREN    15
#define MAX_LABEL       64
#define MAX_VALUE       64
#define MAX_SYM         256
#define MAX_SCOPE_DEPTH 64

/* ===================== TOKEN / NODE (same as Phase 4) ===================== */
typedef struct Token {
    char type[MAX_LABEL];
    char value[MAX_VALUE];
    int  line;
} Token;

typedef struct Node {
    char label[MAX_LABEL];
    char value[MAX_VALUE];
    struct Node* children[MAX_CHILDREN];
    int child_count;
    int line;
    char source[4096];
    char rd_error[256];
} Node;

/* ===================== SYMBOL TABLE ===================== */
typedef struct {
    char name[MAX_LABEL];   /* variable name               */
    char type[MAX_VALUE];   /* "int" or "float"            */
    int  scope;             /* depth at which it was declared */
    int  offset;            /* simulated memory offset (bytes) */
    int  line;              /* line of declaration         */
} Symbol;

Symbol  sym_table[MAX_SYM];
int     sym_count = 0;

int current_scope            = 0;
int scope_offset[MAX_SCOPE_DEPTH]; /* running offset per scope level */

/* ---- scope management ---- */
void push_scope(void) {
    current_scope++;
    if (current_scope < MAX_SCOPE_DEPTH)
        scope_offset[current_scope] = 0;
    printf("  [SCOPE] >>> Entering scope level %d\n", current_scope);
}

void pop_scope(void) {
    printf("  [SCOPE] <<< Leaving scope level %d  (symbols declared here:)\n",
           current_scope);

    /* print every symbol that belongs to the scope we're leaving */
    int found = 0;
    for (int i = 0; i < sym_count; i++) {
        if (sym_table[i].scope == current_scope) {
            printf("            %-12s  type=%-6s  offset=%d\n",
                   sym_table[i].name,
                   sym_table[i].type,
                   sym_table[i].offset);
            found = 1;
        }
    }
    if (!found) printf("            (none)\n");

    current_scope--;
}

/* ---- insert ---- */
/* Returns 1 on success, 0 if the name is already declared in THIS scope */
int sym_insert(const char* name, const char* type, int line) {
    /* check for duplicate in the SAME scope */
    for (int i = 0; i < sym_count; i++) {
        if (sym_table[i].scope == current_scope &&
            strcmp(sym_table[i].name, name) == 0) {
            return 0;   /* duplicate */
        }
    }

    if (sym_count >= MAX_SYM) {
        fprintf(stderr, "Symbol table full!\n");
        return 0;
    }

    /* compute offset: int=4 bytes, float=4 bytes (simplified) */
    int sz = 4;
    int off = scope_offset[current_scope];
    scope_offset[current_scope] += sz;

    strcpy(sym_table[sym_count].name,   name);
    strcpy(sym_table[sym_count].type,   type);
    sym_table[sym_count].scope  = current_scope;
    sym_table[sym_count].offset = off;
    sym_table[sym_count].line   = line;
    sym_count++;
    return 1;
}

/* ---- lookup ---- */
/* Searches from innermost (current) scope outward. Returns pointer or NULL. */
Symbol* sym_lookup(const char* name) {
    /* walk inward-to-outward by scanning entire table,
       picking the entry with the highest scope <= current_scope */
    Symbol* best = NULL;
    for (int i = 0; i < sym_count; i++) {
        if (strcmp(sym_table[i].name, name) == 0 &&
            sym_table[i].scope <= current_scope) {
            if (best == NULL || sym_table[i].scope > best->scope)
                best = &sym_table[i];
        }
    }
    return best;
}

/* ---- print full table ---- */
void print_symbol_table(void) {
    printf("\n");
    printf("================================================================================\n");
    printf("  SYMBOL TABLE  (%d entr%s)\n", sym_count, sym_count == 1 ? "y" : "ies");
    printf("================================================================================\n");
    printf("  %-16s  %-8s  %-7s  %-10s  %s\n",
           "Name", "Type", "Scope", "Offset", "Line");
    printf("  %-16s  %-8s  %-7s  %-10s  %s\n",
           "----------------", "--------", "-------", "----------", "----");
    for (int i = 0; i < sym_count; i++) {
        printf("  %-16s  %-8s  %-7d  %-10d  %d\n",
               sym_table[i].name,
               sym_table[i].type,
               sym_table[i].scope,
               sym_table[i].offset,
               sym_table[i].line);
    }
    printf("================================================================================\n\n");
}

/* ===================== MINIMAL PARSER (reads tokens.txt) =====================
 * We re-implement just enough of Phase 4's recursive descent to:
 *   - walk through the token stream
 *   - detect declarations and identifier uses
 *   - push/pop scopes on { }
 * We do NOT touch the CFG / LL(1) / S-R machinery at all.
 * =========================================================================== */

Token  tokens[MAX_TOKENS];
int    token_count = 0;
int    pos         = 0;
int    last_line   = 1;

static Token* cur(void)          { return pos < token_count ? &tokens[pos] : NULL; }
static Token* consume(void)      { Token* t = cur(); if(t){ last_line=t->line; pos++; } return t; }
static int    peek_is_delim(const char* v) {
    Token* t = cur();
    return t && strcmp(t->type,"DELIMITER")==0 && strcmp(t->value,v)==0;
}
static void   skip_until_semi_or_close(void) {
    while (cur()) {
        if (peek_is_delim(";")) { consume(); return; }
        if (peek_is_delim("}")) return;
        consume();
    }
}

/* forward */
void walk_stmt_list(void);
void walk_stmt(void);
void walk_expr(void);
void walk_bool_expr(void);

/* skip over an arithmetic expression (stops before ; ) { } ) ) */
void walk_expr(void) {
    while (cur()) {
        Token* t = cur();
        if (strcmp(t->type,"DELIMITER")==0 &&
            (strcmp(t->value,";")==0 || strcmp(t->value,")")==0 ||
             strcmp(t->value,"{")==0 || strcmp(t->value,"}")==0))
            break;
        if (strcmp(t->type,"RELATIONAL")==0) break; /* part of bool */
        if (strcmp(t->type,"LOGICAL")==0)    break;
        consume();
    }
}

void walk_bool_expr(void) {
    /* just consume until ) at the matching depth */
    int depth = 0;
    while (cur()) {
        Token* t = cur();
        if (strcmp(t->type,"DELIMITER")==0 && strcmp(t->value,"(")==0) { depth++; consume(); }
        else if (strcmp(t->type,"DELIMITER")==0 && strcmp(t->value,")")==0) {
            if (depth == 0) break;
            depth--; consume();
        }
        else consume();
    }
}

void walk_stmt_list(void) {
    while (cur()) {
        Token* t = cur();
        /* stop at } */
        if (strcmp(t->type,"DELIMITER")==0 && strcmp(t->value,"}")==0) break;
        walk_stmt();
    }
}

void walk_stmt(void) {
    Token* t = cur();
    if (!t) return;

    /* ---- BLOCK ---- */
    if (strcmp(t->type,"DELIMITER")==0 && strcmp(t->value,"{")==0) {
        consume();
        push_scope();
        walk_stmt_list();
        if (peek_is_delim("}")) consume();
        pop_scope();
        return;
    }

    /* ---- DECLARATION  (int/float id [= expr] ;) ---- */
    if (strcmp(t->type,"KEYWORD")==0 &&
        (strcmp(t->value,"int")==0 || strcmp(t->value,"float")==0)) {

        char type_name[16];
        strcpy(type_name, t->value);
        int decl_line = t->line;
        consume(); /* eat the type keyword */

        Token* id = cur();
        if (id && strcmp(id->type,"IDENTIFIER")==0) {
            char var_name[MAX_LABEL];
            strcpy(var_name, id->value);
            consume(); /* eat the identifier */

            if (sym_insert(var_name, type_name, decl_line)) {
                Symbol* s = sym_lookup(var_name);
                printf("  [INSERT] %-12s  type=%-6s  scope=%d  offset=%d  (line %d)\n",
                       var_name, type_name, s->scope, s->offset, decl_line);
            } else {
                printf("  [WARN]   Multiple declaration of '%s' in scope %d (line %d)\n",
                       var_name, current_scope, decl_line);
            }
        }
        skip_until_semi_or_close();
        return;
    }

    /* ---- ASSIGNMENT  (id = expr ;) ---- */
    if (strcmp(t->type,"IDENTIFIER")==0) {
        Token* next = (pos+1 < token_count) ? &tokens[pos+1] : NULL;
        if (next && strcmp(next->type,"ASSIGNMENT")==0) {
            char var_name[MAX_LABEL];
            strcpy(var_name, t->value);
            consume(); consume(); /* eat id and = */

            Symbol* s = sym_lookup(var_name);
            if (s)
                printf("  [LOOKUP] %-12s  found in scope %d  type=%s\n",
                       var_name, s->scope, s->type);
            else
                printf("  [WARN]   Use of undeclared variable '%s' (line %d)\n",
                       var_name, t->line);

            walk_expr();
            if (peek_is_delim(";")) consume();
            return;
        }
        consume(); /* something unexpected, skip */
        return;
    }

    /* ---- IF ---- */
    if (strcmp(t->type,"KEYWORD")==0 && strcmp(t->value,"if")==0) {
        consume();
        if (peek_is_delim("(")) consume();
        walk_bool_expr();
        if (peek_is_delim(")")) consume();
        walk_stmt(); /* then-block (handled as block above) */
        if (cur() && strcmp(cur()->type,"KEYWORD")==0 && strcmp(cur()->value,"else")==0) {
            consume();
            walk_stmt();
        }
        return;
    }

    /* ---- WHILE ---- */
    if (strcmp(t->type,"KEYWORD")==0 && strcmp(t->value,"while")==0) {
        consume();
        if (peek_is_delim("(")) consume();
        walk_bool_expr();
        if (peek_is_delim(")")) consume();
        walk_stmt();
        return;
    }

    /* ---- PRINT ---- */
    if (strcmp(t->type,"KEYWORD")==0 && strcmp(t->value,"print")==0) {
        consume();
        skip_until_semi_or_close();
        return;
    }

    /* anything else: skip token */
    consume();
}

/* ===================== MAIN ===================== */
int main(void) {
    /* --- load tokens.txt produced by Phase 1 --- */
    FILE* f = fopen("tokens.txt", "r");
    if (!f) { printf("Cannot open tokens.txt\n"); return 1; }

    char type_buf[MAX_LABEL], val_buf[MAX_VALUE];
    int  line_buf;
    while (fscanf(f, "%s %s %d", type_buf, val_buf, &line_buf) == 3) {
        strcpy(tokens[token_count].type,  type_buf);
        strcpy(tokens[token_count].value, val_buf);
        tokens[token_count].line = line_buf;
        token_count++;
    }
    fclose(f);

    printf("================================================================================\n");
    printf("  PHASE 5 - SYMBOL TABLE & SCOPE ANALYSIS\n");
    printf("================================================================================\n");
    printf("  Loaded %d tokens from tokens.txt\n\n", token_count);

    /* --- initialise scope 0 (global) --- */
    scope_offset[0] = 0;
    printf("  [SCOPE] >>> Entering scope level 0  (global)\n");

    /* --- walk the program --- */
    walk_stmt_list();

    printf("  [SCOPE] <<< Leaving scope level 0  (global)\n");

    /* --- print the completed symbol table --- */
    print_symbol_table();

    return 0;
}
