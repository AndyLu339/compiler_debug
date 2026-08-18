/* ToyC 语法分析器 (Menhir) */

%{
open AST
open Common
%}

/* 终结符 */
%token <int>    NUMBER
%token <string> ID

%token INT VOID CONST
%token IF ELSE WHILE BREAK CONTINUE RETURN

%token PLUS MINUS TIMES DIVIDE MOD
%token EQ EQEQ NE LT GT LE GE
%token NOT LAND LOR

%token LPAREN RPAREN LBRACE RBRACE
%token SEMICOLON COMMA

%token EOF

/* 优先级与结合性（由低到高） */
%left LOR
%left LAND
%nonassoc EQEQ NE
%nonassoc LT GT LE GE
%left PLUS MINUS
%left TIMES DIVIDE MOD
%right NOT

%start comp_unit
%type <AST.comp_unit> comp_unit

%%

comp_unit:
  | items = nonempty_list(top_item) EOF
    { items }
  ;

top_item:
  | d = decl
    { { node = TopDecl d; loc = ($startpos, $endpos) } }
  | f = func_def
    { { node = TopFunc f; loc = ($startpos, $endpos) } }
  ;

/* 声明 */
decl:
  | CONST INT id = ID EQ e = expr SEMICOLON
    { { node = ConstDecl { const_name = id; const_init = e }; loc = ($startpos, $endpos) } }
  | INT id = ID EQ e = expr SEMICOLON
    { { node = VarDecl { var_name = id; var_init = e }; loc = ($startpos, $endpos) } }
  ;

/* 函数定义 */
func_def:
  | INT id = ID
    LPAREN params = separated_list(COMMA, param) RPAREN
    body = block
    { { func_ret = Common.Int; func_name = id;
        func_params = params; func_body = body; func_loc = ($startpos, $endpos) } }
  | VOID id = ID
    LPAREN params = separated_list(COMMA, param) RPAREN
    body = block
    { { func_ret = Common.Void; func_name = id;
        func_params = params; func_body = body; func_loc = ($startpos, $endpos) } }
  ;

param:
  | INT id = ID  { { param_name = id } }
  ;

/* 语句块 */
block:
  | LBRACE stmts = list(stmt) RBRACE  { stmts }
  ;

/* 语句 */
stmt:
  | b = block
    { { node = Block b; loc = ($startpos, $endpos) } }
  | SEMICOLON
    { { node = Empty; loc = ($startpos, $endpos) } }
  | id = ID EQ e = expr SEMICOLON
    { { node = Assign (id, e); loc = ($startpos, $endpos) } }
  | e = expr SEMICOLON
    { { node = ExprStmt e; loc = ($startpos, $endpos) } }
  | d = decl
    { { node = DeclStmt d; loc = ($startpos, $endpos) } }
  | IF LPAREN cond = expr RPAREN then_stmt = stmt else_stmt = option(else_branch)
    { { node = If (cond, then_stmt, else_stmt); loc = ($startpos, $endpos) } }
  | WHILE LPAREN cond = expr RPAREN body = stmt
    { { node = While (cond, body); loc = ($startpos, $endpos) } }
  | BREAK SEMICOLON
    { { node = Break; loc = ($startpos, $endpos) } }
  | CONTINUE SEMICOLON
    { { node = Continue; loc = ($startpos, $endpos) } }
  | RETURN e = option(expr) SEMICOLON
    { { node = Return e; loc = ($startpos, $endpos) } }
  ;

else_branch:
  | ELSE s = stmt { s }
  ;

/* 表达式 */
expr:
  | e1 = expr LOR   e2 = expr
    { { node = Binary (e1, LOr,  e2); loc = ($startpos, $endpos) } }
  | e1 = expr LAND  e2 = expr
    { { node = Binary (e1, LAnd, e2); loc = ($startpos, $endpos) } }
  | e1 = expr EQEQ  e2 = expr
    { { node = Binary (e1, Eq,   e2); loc = ($startpos, $endpos) } }
  | e1 = expr NE    e2 = expr
    { { node = Binary (e1, Ne,   e2); loc = ($startpos, $endpos) } }
  | e1 = expr LT    e2 = expr
    { { node = Binary (e1, Lt,   e2); loc = ($startpos, $endpos) } }
  | e1 = expr GT    e2 = expr
    { { node = Binary (e1, Gt,   e2); loc = ($startpos, $endpos) } }
  | e1 = expr LE    e2 = expr
    { { node = Binary (e1, Le,   e2); loc = ($startpos, $endpos) } }
  | e1 = expr GE    e2 = expr
    { { node = Binary (e1, Ge,   e2); loc = ($startpos, $endpos) } }
  | e1 = expr PLUS  e2 = expr
    { { node = Binary (e1, Add,  e2); loc = ($startpos, $endpos) } }
  | e1 = expr MINUS e2 = expr
    { { node = Binary (e1, Sub,  e2); loc = ($startpos, $endpos) } }
  | e1 = expr TIMES e2 = expr
    { { node = Binary (e1, Mul,  e2); loc = ($startpos, $endpos) } }
  | e1 = expr DIVIDE e2 = expr
    { { node = Binary (e1, Div,  e2); loc = ($startpos, $endpos) } }
  | e1 = expr MOD   e2 = expr
    { { node = Binary (e1, Mod,  e2); loc = ($startpos, $endpos) } }
  | MINUS e = expr %prec NOT
    { { node = Unary (Neg, e); loc = ($startpos, $endpos) } }
  | PLUS  e = expr %prec NOT
    { { node = Unary (Pos, e); loc = ($startpos, $endpos) } }
  | NOT   e = expr
    { { node = Unary (Not, e); loc = ($startpos, $endpos) } }
  | e = primary_expr
    { e }
  ;

primary_expr:
  | id = ID
    { { node = Var id; loc = ($startpos, $endpos) } }
  | n = NUMBER
    { { node = Int n; loc = ($startpos, $endpos) } }
  | LPAREN e = expr RPAREN
    { e }
  | id = ID LPAREN args = separated_list(COMMA, expr) RPAREN
    { { node = Call (id, args); loc = ($startpos, $endpos) } }
  ;
