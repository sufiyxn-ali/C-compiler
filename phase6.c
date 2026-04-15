/*
 * ============================================================
 *  PHASE 6 - SEMANTIC ANALYSIS
 *  Rebuilds the parse tree using the same recursive descent
 *  parser and Node structure from Phase 4 (unchanged).
 *  Then walks the tree to detect:
 *    1. Use of undeclared variables
 *    2. Multiple declarations in the same scope
 *    3. Type mismatches in assignments and expressions
 *    4. Invalid boolean conditions
 * ============================================================
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

/* ===================== DEFINES (same as Phase 4) ===================== */
#define MAX_TOKENS    2000
#define MAX_CHILDREN  15
#define MAX_LABEL     64
#define MAX_VALUE     64
#define MAX_STMTS     200

/* ===================== TOKEN & NODE (copied from Phase 4) ===================== */
typedef struct Token {
    char type[MAX_LABEL];
    char value[MAX_VALUE];
    int  line;
} Token;

typedef struct Node {
    char  label[MAX_LABEL];
    char  value[MAX_VALUE];
    struct Node* children[MAX_CHILDREN];
    int   child_count;
    int   line;
    char  source[4096];
    char  rd_error[256];
} Node;

Token tokens[MAX_TOKENS];
int   token_count    = 0;
int   pos            = 0;
int   last_line      = 1;
int   error_count    = 0;

char  error_messages[MAX_STMTS][256];
int   error_msg_total = 0;
char  last_rd_error[256] = {0};

/* ===================== NODE HELPERS (copied from Phase 4) ===================== */
Node* create_node(const char* label, const char* value, int line) {
    Node* n = (Node*)malloc(sizeof(Node));
    if (!n) return NULL;
    strcpy(n->label, label);
    if (value) strcpy(n->value, value); else n->value[0] = '\0';
    n->child_count = 0;
    n->line        = line;
    n->source[0]   = '\0';
    n->rd_error[0] = '\0';
    for (int i = 0; i < MAX_CHILDREN; i++) n->children[i] = NULL;
    return n;
}
void add_child(Node* p, Node* c) {
    if (p && c && p->child_count < MAX_CHILDREN)
        p->children[p->child_count++] = c;
}

/* ===================== PARSER HELPERS (copied from Phase 4) ===================== */
void print_error(const char* msg, int line) {
    sprintf(last_rd_error, ">> Syntax Error at line %d: %s", line, msg);
    if (error_msg_total < MAX_STMTS) {
        sprintf(error_messages[error_msg_total],
                ">> Syntax Error at line %d: %s", line, msg);
        error_msg_total++;
    }
    error_count++;
}
Token* current_tok(void)  { return pos < token_count ? &tokens[pos] : NULL; }
Token* consume_tok(void)  { Token* t = current_tok(); if(t){ last_line=t->line; pos++; } return t; }

Token* expect_type(const char* expected) {
    Token* t = current_tok();
    if (!t || strcmp(t->type, expected) != 0) {
        char err[128];
        sprintf(err, "Expected type %s, got %s", expected, t ? t->type : "EOF");
        print_error(err, last_line); return NULL;
    }
    last_line = t->line; pos++; return t;
}
Token* expect_delim(const char* expected) {
    Token* t = current_tok();
    if (!t) {
        char err[64]; sprintf(err,"Expected '%s', got EOF", expected);
        print_error(err, last_line); return NULL;
    }
    if (strcmp(t->type,"DELIMITER")!=0 || strcmp(t->value,expected)!=0) {
        char err[128]; sprintf(err,"Expected '%s', got '%s'", expected, t->value);
        print_error(err, last_line); return NULL;
    }
    last_line = t->line; pos++; return t;
}
void skip_to_next_statement(void) {
    while (pos < token_count) {
        Token* t = current_tok();
        if (strcmp(t->type,"KEYWORD")==0) {
            if (strcmp(t->value,"int")==0||strcmp(t->value,"float")==0||
                strcmp(t->value,"if")==0||strcmp(t->value,"while")==0||
                strcmp(t->value,"print")==0) return;
        } else if (strcmp(t->type,"IDENTIFIER")==0) {
            Token* next = (pos+1<token_count)?&tokens[pos+1]:NULL;
            if (next && strcmp(next->type,"ASSIGNMENT")==0) return;
            pos++; continue;
        } else if (strcmp(t->type,"DELIMITER")==0&&strcmp(t->value,"}")==0) {
            pos++; return;
        }
        pos++;
    }
}
void synchronize(void) {
    while (pos < token_count) {
        Token* t = current_tok();
        if (strcmp(t->type,"DELIMITER")==0&&strcmp(t->value,";")==0) { pos++; return; }
        if (strcmp(t->type,"DELIMITER")==0&&strcmp(t->value,"}")==0) return;
        if (strcmp(t->type,"KEYWORD")==0) {
            if (strcmp(t->value,"int")==0||strcmp(t->value,"float")==0||
                strcmp(t->value,"if")==0||strcmp(t->value,"while")==0||
                strcmp(t->value,"print")==0) return;
        }
        if (strcmp(t->type,"IDENTIFIER")==0) {
            Token* next = (pos+1<token_count)?&tokens[pos+1]:NULL;
            if (next && strcmp(next->type,"ASSIGNMENT")==0) return;
        }
        pos++;
    }
}

/* ===================== RECURSIVE DESCENT PARSER (copied from Phase 4) ===================== */
Node* parse_statement_list(void);
Node* parse_statement(void);
Node* parse_decl_statement(void);
Node* parse_assign_statement(void);
Node* parse_if_statement(void);
Node* parse_while_statement(void);
Node* parse_print_statement(void);
Node* parse_block(void);
Node* parse_bool_expr(void);
Node* parse_bool_atom(void);
Node* parse_expr(void);
Node* parse_term(void);
Node* parse_factor(void);
Node* parse_error_statement(void);

Node* parse_factor(void) {
    Token* t = current_tok(); if (!t) return NULL;
    Node* node = create_node("factor", NULL, t->line);
    if (strcmp(t->value,"(")==0) {
        expect_delim("(");
        Node* expr = parse_expr(); if (!expr) return NULL;
        add_child(node, expr);
        if (!expect_delim(")")) return NULL;
    } else if (strcmp(t->type,"INTEGER")==0) {
        add_child(node, create_node("INTEGER", t->value, t->line)); consume_tok();
    } else if (strcmp(t->type,"FLOAT")==0) {
        add_child(node, create_node("FLOAT", t->value, t->line)); consume_tok();
    } else if (strcmp(t->type,"IDENTIFIER")==0) {
        add_child(node, create_node("ID", t->value, t->line)); consume_tok();
    } else {
        char err[64]; sprintf(err,"unexpected '%s' in expression", t->value);
        print_error(err, t->line); consume_tok();
    }
    return node;
}
Node* parse_term(void) {
    Node* node = parse_factor(); if (!node) return NULL;
    while (current_tok()) {
        Token* op = current_tok();
        if (strcmp(op->type,"ARITHMETIC")==0 &&
            (strcmp(op->value,"*")==0||strcmp(op->value,"/")==0||strcmp(op->value,"%")==0)) {
            consume_tok();
            Node* right = parse_factor(); if (!right) return NULL;
            Node* parent = create_node("term", NULL, op->line);
            add_child(parent, node);
            add_child(parent, create_node("ARITHMETIC", op->value, op->line));
            add_child(parent, right);
            node = parent;
        } else break;
    }
    return node;
}
Node* parse_expr(void) {
    Node* node = parse_term(); if (!node) return NULL;
    while (current_tok()) {
        Token* op = current_tok();
        if (strcmp(op->type,"ARITHMETIC")==0 &&
            (strcmp(op->value,"+")==0||strcmp(op->value,"-")==0)) {
            consume_tok();
            Node* right = parse_term(); if (!right) return NULL;
            Node* parent = create_node("expr", NULL, op->line);
            add_child(parent, node);
            add_child(parent, create_node("ARITHMETIC", op->value, op->line));
            add_child(parent, right);
            node = parent;
        } else break;
    }
    return node;
}
Node* parse_bool_atom(void) {
    Token* cur = current_tok(); if (!cur) return NULL;
    if (strcmp(cur->value,"!")==0) {
        Node* node = create_node("bool_expr", NULL, cur->line);
        consume_tok();
        add_child(node, create_node("NOT","!",last_line));
        Node* next = parse_bool_atom(); if (next) add_child(node, next);
        return node;
    } else if (strcmp(cur->value,"(")==0) {
        expect_delim("(");
        Node* node = parse_bool_expr();
        expect_delim(")");
        return node;
    } else {
        Node* n = create_node("bool_expr", NULL, cur->line);
        Node* expr = parse_expr(); if (expr) add_child(n, expr);
        Token* t = current_tok();
        if (t && strcmp(t->type,"RELATIONAL")==0) {
            consume_tok();
            add_child(n, create_node("REL_OP", t->value, t->line));
            Node* right = parse_expr(); if (right) add_child(n, right);
        }
        return n;
    }
}
Node* parse_bool_expr(void) {
    Node* node = parse_bool_atom(); if (!node) return NULL;
    while (current_tok()) {
        Token* t = current_tok();
        if (t && strcmp(t->type,"LOGICAL")==0) {
            Node* parent = create_node("bool_expr", NULL, t->line);
            add_child(parent, node);
            add_child(parent, create_node("LOGICAL", t->value, t->line));
            consume_tok();
            Node* right = parse_bool_atom(); if (right) add_child(parent, right);
            node = parent;
        } else break;
    }
    return node;
}
Node* parse_decl_statement(void) {
    Token* t = current_tok(); if (!t) return NULL;
    Node* node = create_node("decl_stmt", NULL, t->line);
    t = expect_type("KEYWORD"); if (!t) return NULL;
    add_child(node, create_node("TYPE", t->value, t->line));
    t = expect_type("IDENTIFIER"); if (!t) return NULL;
    add_child(node, create_node("ID", t->value, t->line));
    if (current_tok() && strcmp(current_tok()->type,"ASSIGNMENT")==0) {
        t = consume_tok();
        add_child(node, create_node("ASSIGNMENT", t->value, t->line));
        Node* expr = parse_expr(); if (expr) add_child(node, expr);
    }
    if (!expect_delim(";")) { synchronize(); strcpy(node->rd_error, last_rd_error); return node; }
    add_child(node, create_node("SEMI", ";", last_line));
    return node;
}
Node* parse_assign_statement(void) {
    Token* t = current_tok(); if (!t) return NULL;
    Node* node = create_node("assign_stmt", NULL, t->line);
    t = expect_type("IDENTIFIER"); if (!t) return NULL;
    add_child(node, create_node("ID", t->value, t->line));
    Token* at = expect_type("ASSIGNMENT");
    if (!at) { synchronize(); strcpy(node->rd_error, last_rd_error); return node; }
    add_child(node, create_node("ASSIGNMENT", at->value, at->line));
    Node* expr = parse_expr(); if (expr) add_child(node, expr);
    if (!expect_delim(";")) { synchronize(); strcpy(node->rd_error, last_rd_error); return node; }
    add_child(node, create_node("SEMI", ";", last_line));
    return node;
}
Node* parse_error_statement(void) {
    Token* t = current_tok(); if (!t) return NULL;
    Node* node = create_node("error_stmt", NULL, t->line);
    strcpy(node->rd_error, last_rd_error);
    int start_pos = pos;
    while (current_tok()) {
        Token* cur = current_tok();
        if (strcmp(cur->type,"DELIMITER")==0&&strcmp(cur->value,";")==0) {
            add_child(node, create_node("SEMI", cur->value, cur->line));
            consume_tok(); break;
        }
        if (strcmp(cur->type,"KEYWORD")==0) {
            if (strcmp(cur->value,"int")==0||strcmp(cur->value,"float")==0||
                strcmp(cur->value,"if")==0||strcmp(cur->value,"while")==0||
                strcmp(cur->value,"print")==0) break;
        }
        if (strcmp(cur->type,"IDENTIFIER")==0) {
            Token* next = (pos+1<token_count)?&tokens[pos+1]:NULL;
            if (next && strcmp(next->type,"ASSIGNMENT")==0) break;
        }
        {
            char lbl[MAX_LABEL];
            if      (strcmp(cur->type,"IDENTIFIER")==0) strcpy(lbl,"ID");
            else if (strcmp(cur->type,"INTEGER")==0)     strcpy(lbl,"INTEGER");
            else if (strcmp(cur->type,"FLOAT")==0)       strcpy(lbl,"FLOAT");
            else if (strcmp(cur->type,"KEYWORD")==0)     strcpy(lbl,"TYPE");
            else if (strcmp(cur->type,"ASSIGNMENT")==0)  strcpy(lbl,"ASSIGNMENT");
            else if (strcmp(cur->type,"ARITHMETIC")==0)  strcpy(lbl,"ARITHMETIC");
            else if (strcmp(cur->type,"LOGICAL")==0)     strcpy(lbl,"LOGICAL");
            else if (strcmp(cur->type,"RELATIONAL")==0)  strcpy(lbl,"REL_OP");
            else if (strcmp(cur->type,"DELIMITER")==0) {
                if      (strcmp(cur->value,"(")==0) strcpy(lbl,"LPAREN");
                else if (strcmp(cur->value,")")==0) strcpy(lbl,"RPAREN");
                else if (strcmp(cur->value,"{")==0) strcpy(lbl,"LBRACE");
                else if (strcmp(cur->value,"}")==0) strcpy(lbl,"RBRACE");
                else strcpy(lbl, cur->type);
            } else strcpy(lbl, cur->type);
            add_child(node, create_node(lbl, cur->value, cur->line));
        }
        consume_tok();
    }
    char source_buf[4096] = {0};
    for (int i = start_pos; i < pos && i < token_count; i++) {
        strcat(source_buf, tokens[i].value);
        if (i < pos-1) strcat(source_buf, " ");
    }
    strcpy(node->source, source_buf);
    return node;
}
Node* parse_if_statement(void) {
    Token* t = current_tok(); if (!t) return NULL;
    Node* node = create_node("if_stmt", NULL, t->line);
    if (strcmp(t->value,"if")!=0) { print_error("expected 'if'",last_line); return NULL; }
    consume_tok();
    add_child(node, create_node("IF","if",last_line));
    expect_delim("("); add_child(node, create_node("LPAREN","(",last_line));
    Node* cond = parse_bool_expr(); if (cond) add_child(node, cond);
    expect_delim(")"); add_child(node, create_node("RPAREN",")",last_line));
    Node* tb = parse_block(); if (tb) add_child(node, tb);
    if (current_tok()&&strcmp(current_tok()->value,"else")==0) {
        consume_tok(); add_child(node, create_node("ELSE","else",last_line));
        Node* eb = parse_block(); if (eb) add_child(node, eb);
    }
    return node;
}
Node* parse_while_statement(void) {
    Token* t = current_tok(); if (!t) return NULL;
    Node* node = create_node("while_stmt", NULL, t->line);
    if (strcmp(t->value,"while")!=0) { print_error("expected 'while'",last_line); return NULL; }
    consume_tok();
    add_child(node, create_node("WHILE","while",last_line));
    expect_delim("("); add_child(node, create_node("LPAREN","(",last_line));
    Node* cond = parse_bool_expr(); if (cond) add_child(node, cond);
    expect_delim(")"); add_child(node, create_node("RPAREN",")",last_line));
    Node* body = parse_block(); if (body) add_child(node, body);
    return node;
}
Node* parse_print_statement(void) {
    Token* t = current_tok(); if (!t) return NULL;
    Node* node = create_node("print_stmt", NULL, t->line);
    if (strcmp(t->value,"print")!=0) { print_error("expected 'print'",last_line); return NULL; }
    consume_tok();
    add_child(node, create_node("PRINT","print",last_line));
    expect_delim("("); add_child(node, create_node("LPAREN","(",last_line));
    Node* expr = parse_expr(); if (expr) add_child(node, expr);
    expect_delim(")"); add_child(node, create_node("RPAREN",")",last_line));
    if (!expect_delim(";")) { synchronize(); strcpy(node->rd_error, last_rd_error); return node; }
    add_child(node, create_node("SEMI",";",last_line));
    return node;
}
Node* parse_block(void) {
    Node* node = create_node("block", NULL, current_tok()?current_tok()->line:last_line);
    if (!expect_delim("{")) return NULL;
    add_child(node, create_node("LBRACE","{",last_line));
    Node* sl = parse_statement_list(); if (sl) add_child(node, sl);
    if (!expect_delim("}")) return NULL;
    add_child(node, create_node("RBRACE","}",last_line));
    return node;
}
Node* parse_statement(void) {
    Token* t = current_tok(); if (!t) return NULL;
    if (strcmp(t->type,"KEYWORD")==0) {
        if (strcmp(t->value,"int")==0||strcmp(t->value,"float")==0) return parse_decl_statement();
        if (strcmp(t->value,"if")==0)    return parse_if_statement();
        if (strcmp(t->value,"while")==0) return parse_while_statement();
        if (strcmp(t->value,"print")==0) return parse_print_statement();
        char err[64]; sprintf(err,"Unknown keyword '%s'",t->value);
        print_error(err,t->line); return parse_error_statement();
    }
    if (strcmp(t->type,"IDENTIFIER")==0) {
        Token* next = (pos+1<token_count)?&tokens[pos+1]:NULL;
        if (next&&strcmp(next->type,"ASSIGNMENT")==0) return parse_assign_statement();
        char err[128];
        if (next) sprintf(err,"Expected '=', got '%s'",next->value);
        else      sprintf(err,"Expected '=', got EOF");
        print_error(err,t->line); return parse_error_statement();
    }
    if (strcmp(t->type,"DELIMITER")==0&&strcmp(t->value,"{")==0) return parse_block();
    char err[64]; sprintf(err,"Unexpected token '%s'",t->value);
    print_error(err,t->line); return parse_error_statement();
}
Node* parse_statement_list(void) {
    Node* node = create_node("stmt_list", NULL, last_line);
    while (current_tok()) {
        Token* t = current_tok();
        if (strcmp(t->type,"DELIMITER")==0&&strcmp(t->value,"}")==0) break;
        int saved_pos = pos;
        Node* stmt = parse_statement();
        if (stmt) {
            char source_buf[4096] = {0};
            for (int i = saved_pos; i < pos && i < token_count; i++) {
                strcat(source_buf, tokens[i].value);
                if (i < pos-1) strcat(source_buf, " ");
            }
            strcpy(stmt->source, source_buf);
            add_child(node, stmt);
        } else {
            if (pos == saved_pos) skip_to_next_statement();
        }
    }
    return node;
}
Node* parse_program_rd(void) {
    last_rd_error[0] = '\0';
    Node* node = create_node("program", NULL, 1);
    Node* sl = parse_statement_list(); if (sl) add_child(node, sl);
    return node;
}

/* ===================== PRINT TREE ===================== */
void print_tree(Node* node, int indent) {
    if (!node) return;
    for (int i = 0; i < indent; i++) printf("  ");
    if (node->value[0] != '\0') printf("%s(%s)\n", node->label, node->value);
    else                        printf("%s\n",      node->label);
    for (int i = 0; i < node->child_count; i++) print_tree(node->children[i], indent+1);
}

/* ===================== SYMBOL TABLE ===================== */
#define MAX_SYM 256

typedef struct {
    char name[MAX_LABEL];
    char type[MAX_VALUE];
    int  scope;
    int  line;
} Symbol;

Symbol sym_table[MAX_SYM];
int    sym_count     = 0;
int    current_scope = 0;

int sym_insert(const char* name, const char* type, int line) {
    for (int i = 0; i < sym_count; i++)
        if (sym_table[i].scope == current_scope &&
            strcmp(sym_table[i].name, name) == 0) return 0;
    if (sym_count >= MAX_SYM) return 0;
    strcpy(sym_table[sym_count].name,  name);
    strcpy(sym_table[sym_count].type,  type);
    sym_table[sym_count].scope = current_scope;
    sym_table[sym_count].line  = line;
    sym_count++;
    return 1;
}
Symbol* sym_lookup(const char* name) {
    Symbol* best = NULL;
    for (int i = 0; i < sym_count; i++)
        if (strcmp(sym_table[i].name, name) == 0 &&
            sym_table[i].scope <= current_scope)
            if (!best || sym_table[i].scope > best->scope)
                best = &sym_table[i];
    return best;
}

/* ===================== SEMANTIC ANALYSIS ===================== */
int sem_errors = 0;

void sem_error(const char* msg, int line) {
    printf("  [SEMANTIC ERROR] Line %d: %s\n", line, msg);
    sem_errors++;
}

/* Walk an expr/term/factor subtree, infer its type, check undeclared vars */
char* infer_type(Node* node) {
    static char result[16];
    if (!node) { strcpy(result,"unknown"); return result; }

    if (strcmp(node->label,"INTEGER")==0) { strcpy(result,"int");   return result; }
    if (strcmp(node->label,"FLOAT")==0)   { strcpy(result,"float"); return result; }
    if (strcmp(node->label,"ID")==0) {
        Symbol* s = sym_lookup(node->value);
        if (!s) {
            char msg[128];
            sprintf(msg,"use of undeclared variable '%s'", node->value);
            sem_error(msg, node->line);
            strcpy(result,"unknown"); return result;
        }
        strcpy(result, s->type); return result;
    }

    /* composite node: propagate float upward */
    strcpy(result,"int");
    for (int i = 0; i < node->child_count; i++) {
        char* ct = infer_type(node->children[i]);
        if (strcmp(ct,"float")==0)   strcpy(result,"float");
        if (strcmp(ct,"unknown")==0 && strcmp(result,"float")!=0)
            strcpy(result,"unknown");
    }
    return result;
}

/* Check that a bool_expr node contains at least one REL_OP somewhere */
int has_relop(Node* node) {
    if (!node) return 0;
    if (strcmp(node->label,"REL_OP")==0) return 1;
    for (int i = 0; i < node->child_count; i++)
        if (has_relop(node->children[i])) return 1;
    return 0;
}

/* Forward declaration */
void sem_walk(Node* node);

void sem_walk(Node* node) {
    if (!node) return;

    /* ---- BLOCK: push/pop scope ---- */
    if (strcmp(node->label,"block")==0) {
        current_scope++;
        printf("  [SCOPE]  entering scope level %d\n", current_scope);
        for (int i = 0; i < node->child_count; i++) sem_walk(node->children[i]);
        printf("  [SCOPE]  leaving  scope level %d\n", current_scope);
        current_scope--;
        return;
    }

    /* ---- DECLARATION ---- */
    if (strcmp(node->label,"decl_stmt")==0) {
        char decl_type[16] = {0};
        char var_name[MAX_LABEL] = {0};
        Node* init_expr = NULL;

        for (int i = 0; i < node->child_count; i++) {
            Node* c = node->children[i];
            if      (strcmp(c->label,"TYPE")==0)       strcpy(decl_type, c->value);
            else if (strcmp(c->label,"ID")==0)         strcpy(var_name,  c->value);
            else if (strcmp(c->label,"ASSIGNMENT")==0 && i+1 < node->child_count)
                init_expr = node->children[i+1];
        }

        /* duplicate declaration check */
        if (!sym_insert(var_name, decl_type, node->line)) {
            char msg[128];
            sprintf(msg,"multiple declaration of '%s' in scope %d",
                    var_name, current_scope);
            sem_error(msg, node->line);
        } else {
            printf("  [DECL]   %-12s  type=%-6s  scope=%d  (line %d)\n",
                   var_name, decl_type, current_scope, node->line);
        }

        /* type mismatch in initialiser */
        if (init_expr) {
            char* rhs = infer_type(init_expr);
            if (strcmp(rhs,"unknown")!=0 &&
                strcmp(decl_type,"int")==0 && strcmp(rhs,"float")==0) {
                char msg[128];
                sprintf(msg,
                    "type mismatch: cannot assign float expression to int variable '%s'",
                    var_name);
                sem_error(msg, node->line);
            }
        }
        return;
    }

    /* ---- ASSIGNMENT ---- */
    if (strcmp(node->label,"assign_stmt")==0) {
        char var_name[MAX_LABEL] = {0};
        Node* rhs_expr = NULL;

        for (int i = 0; i < node->child_count; i++) {
            Node* c = node->children[i];
            if (strcmp(c->label,"ID")==0) strcpy(var_name, c->value);
            else if (strcmp(c->label,"ASSIGNMENT")==0 && i+1 < node->child_count)
                rhs_expr = node->children[i+1];
        }

        Symbol* s = sym_lookup(var_name);
        if (!s) {
            char msg[128];
            sprintf(msg,"use of undeclared variable '%s'", var_name);
            sem_error(msg, node->line);
        }

        if (rhs_expr) {
            char* rhs = infer_type(rhs_expr);
            if (s && strcmp(rhs,"unknown")!=0 &&
                strcmp(s->type,"int")==0 && strcmp(rhs,"float")==0) {
                char msg[128];
                sprintf(msg,
                    "type mismatch: cannot assign float expression to int variable '%s'",
                    var_name);
                sem_error(msg, node->line);
            }
            if (s)
                printf("  [ASSIGN] %-12s = %-6s expression  (line %d)\n",
                       var_name, rhs, node->line);
        }
        return;
    }

    /* ---- IF STATEMENT ---- */
    if (strcmp(node->label,"if_stmt")==0) {
        printf("  [IF]     checking condition (line %d)\n", node->line);
        for (int i = 0; i < node->child_count; i++) {
            Node* c = node->children[i];
            if (strcmp(c->label,"bool_expr")==0) {
                if (!has_relop(c)) {
                    char msg[128];
                    sprintf(msg,"invalid boolean condition - missing relational operator");
                    sem_error(msg, node->line);
                }
            }
            sem_walk(c);
        }
        return;
    }

    /* ---- WHILE STATEMENT ---- */
    if (strcmp(node->label,"while_stmt")==0) {
        printf("  [WHILE]  checking condition (line %d)\n", node->line);
        for (int i = 0; i < node->child_count; i++) {
            Node* c = node->children[i];
            if (strcmp(c->label,"bool_expr")==0) {
                if (!has_relop(c)) {
                    char msg[128];
                    sprintf(msg,"invalid boolean condition - missing relational operator");
                    sem_error(msg, node->line);
                }
            }
            sem_walk(c);
        }
        return;
    }

    /* ---- PRINT STATEMENT ---- */
    if (strcmp(node->label,"print_stmt")==0) {
        printf("  [PRINT]  (line %d)\n", node->line);
        for (int i = 0; i < node->child_count; i++) sem_walk(node->children[i]);
        return;
    }

    /* ---- standalone ID (inside bool/print expressions) ---- */
    if (strcmp(node->label,"ID")==0) {
        if (!sym_lookup(node->value)) {
            char msg[128];
            sprintf(msg,"use of undeclared variable '%s'", node->value);
            sem_error(msg, node->line);
        }
        return;
    }

    /* ---- default: recurse into children ---- */
    for (int i = 0; i < node->child_count; i++) sem_walk(node->children[i]);
}

/* ===================== MAIN ===================== */
int main(void) {
    FILE* f = fopen("tokens.txt","r");
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
    printf("  PHASE 6 - SEMANTIC ANALYSIS\n");
    printf("================================================================================\n");
    printf("  Loaded %d tokens from tokens.txt\n\n", token_count);

    /* rebuild the parse tree using the same RD parser as Phase 4 */
    Node* tree = parse_program_rd();

    if (error_count > 0) {
        printf("  Syntax errors found - semantic analysis aborted.\n\n");
        for (int i = 0; i < error_msg_total; i++)
            printf("  %s\n", error_messages[i]);
        return 1;
    }

    printf("================================================================================\n");
    printf("  PARSE TREE\n");
    printf("================================================================================\n");
    print_tree(tree, 0);

    printf("\n================================================================================\n");
    printf("  SEMANTIC ANALYSIS TRACE\n");
    printf("================================================================================\n\n");

    sem_walk(tree);

    printf("\n================================================================================\n");
    if (sem_errors == 0)
        printf("  Semantic analysis PASSED - no errors found.\n");
    else
        printf("  Semantic analysis found %d error(s).\n", sem_errors);
    printf("================================================================================\n\n");

    printf("  SYMBOL TABLE  (%d entr%s)\n", sym_count, sym_count==1?"y":"ies");
    printf("  %-16s  %-8s  %-7s  %s\n","Name","Type","Scope","Line");
    printf("  %-16s  %-8s  %-7s  %s\n","----------------","--------","-------","----");
    for (int i = 0; i < sym_count; i++)
        printf("  %-16s  %-8s  %-7d  %d\n",
               sym_table[i].name, sym_table[i].type,
               sym_table[i].scope, sym_table[i].line);
    printf("\n");

    return 0;
}