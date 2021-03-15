#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"
#include <unordered_map>
#include <vector>

extern int semant_debug;
extern char *curr_filename;

static ostream& error_stream = cerr;
static int semant_errors = 0;
static Decl curr_decl = 0;

typedef SymbolTable<Symbol, Symbol> ObjectEnvironment; // name, type
ObjectEnvironment objectEnv;

typedef std::unordered_map<Symbol,Symbol> FuncTable;
FuncTable funcT;

typedef std::unordered_map<Symbol,Symbol> GlobalVariableTable;
GlobalVariableTable globalVarT;

typedef std::unordered_map<Symbol,Symbol> LocalVariableTable;
LocalVariableTable localVarT;

/*mark whether paras are installed*/
typedef std::unordered_map<Symbol,bool> InstalledTable;
InstalledTable installedTable;

typedef std::vector<Symbol> ActualPara;
typedef std::unordered_map<Symbol,ActualPara> ActualParaTable;
ActualParaTable actualParaT;
///////////////////////////////////////////////
// helper func
///////////////////////////////////////////////


static ostream& semant_error() {
    semant_errors++;
    return error_stream;
}

static ostream& semant_error(tree_node *t) {
    error_stream << t->get_line_number() << ": ";
    return semant_error();
}

static ostream& internal_error(int lineno) {
    error_stream << "FATAL:" << lineno << ": ";
    return error_stream;
}

//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////

static Symbol 
    Int,
    Float,
    String,
    Bool,
    Void,
    Main,
    print
    ;

bool isValidCallName(Symbol type) {
    return type != (Symbol)print;
}

bool isValidTypeName(Symbol type) {
    return type != Void;
}

//
// Initializing the predefined symbols.
//

static void initialize_constants(void) {
    // 4 basic types and Void type
    Bool        = idtable.add_string("Bool");
    Int         = idtable.add_string("Int");
    String      = idtable.add_string("String");
    Float       = idtable.add_string("Float");
    Void        = idtable.add_string("Void");  
    // Main function
    Main        = idtable.add_string("main");

    // classical function to print things, so defined here for call.
    print        = idtable.add_string("printf");
}

/*
    TODO :
    you should fill the following function defines, so that semant() can realize a semantic 
    analysis in a recursive way. 
    Of course, you can add any other functions to help.
*/

static bool sameType(Symbol name1, Symbol name2) {
    return strcmp(name1->get_string(), name2->get_string()) == 0;
}

//pre-install all function's decls
static void install_calls(Decls decls) {
    for(int i=decls->first();decls->more(i);i=decls->next(i)){
        Decl cur_decl=decls->nth(i);
        Symbol name=cur_decl->getName();
        Symbol type=cur_decl->getType();
        
        if(cur_decl->isCallDecl()){
            //if previously defined
            if(funcT[name]!=NULL){
                semant_error(cur_decl)<<"Function "<<name<<" has been declared previously"<<endl;
            }
            else if(type!=Int && type!=Float && type != String && type!=Bool && type!=Void){
                semant_error(cur_decl)<<"Function "<<name<<" has been incorrectly declared due to type error"<<endl;
            }else if(!isValidCallName(name)){
                semant_error(cur_decl)<<"Function can not be named \"printf\""<<endl;
            }
            funcT[name]=type;
            installedTable[name]=false;
            cur_decl->check();
        }
    }
}

//pre-install all the global vars
static void install_globalVars(Decls decls) {
    for(int i=decls->first();decls->more(i);i=decls->next(i)){
        Decl cur_decl=decls->nth(i);
        Symbol name=cur_decl->getName();
        Symbol type=cur_decl->getType();

        if(!cur_decl->isCallDecl()){
            if(globalVarT[name]!=NULL){
                semant_error(cur_decl)<<"Global Variable "<<name<<" has been declared previously"<<endl;
            }else if(type!=Int && type!=Float && type!=String && type!=Bool && type!= Void){
                semant_error(cur_decl)<<"Global Variable "<<name<<" has been incorrectly declared due to type errors"<<endl;                
            }else if(!isValidTypeName(type)){
                semant_error(cur_decl)<<"Global Variable "<<name<<" cannot be declared type void"<<endl;
            }
            globalVarT[name]=type;
        }
    }
}

static void check_calls(Decls decls) {
    objectEnv.enterscope();
    for(int i=decls->first();decls->more(i);i=decls->next(i)){
        Decl cur_decl=decls->nth(i);
        if(cur_decl->isCallDecl()){
            localVarT.clear();
            cur_decl->check();
        }
    }
    objectEnv.exitscope();
}

static void check_main() {
    if(funcT[Main]==NULL){
        semant_error()<<"Main function is not defined"<<endl;
    }
}

void VariableDecl_class::check() {
    Symbol name=this->getName();
    Symbol type=this->getType();
    if(type==Void){
        semant_error(this)<<"Variable cannot be decleared type Void"<<endl;
    }else{
        objectEnv.addid(name,new Symbol(type));
        localVarT[name]=type;
    }
}

void CallDecl_class::check() {
    Variables vars=this->getVariables();
    Symbol funcName=this->getName();
    Symbol returnType=this->getType();
    StmtBlock body=this->getBody();

    objectEnv.enterscope();
    if(!installedTable[funcName]){
        //install paras
        ActualPara actualparaVec;
        for(int j=vars->first();vars->more(j);j=vars->next(j)){
            Variable cur_var=vars->nth(j);
            Symbol curName=cur_var->getName();
            Symbol curType=cur_var->getType();
            if(curType==Void){
                semant_error(this)<<"Function parameters cannot be declared type Void"<<endl;
            }

            if(objectEnv.lookup(curName)!=NULL){
                semant_error(this)<<"Duplicate Variable Name"<<endl;
            }
            objectEnv.addid(curName,&curType);
            localVarT[curName]=curType;
            actualparaVec.push_back(curType);
        }
        installedTable[funcName]=true;
        actualParaT[funcName]=actualparaVec;
    }else{
        for(int j=vars->first();vars->more(j);j=vars->next(j)){
            Variable cur_var=vars->nth(j);
            Symbol curName=cur_var->getName();
            Symbol curType=cur_var->getType();

            if(objectEnv.lookup(curName)!=NULL){
                semant_error(this)<<"Duplicate Variable Name"<<endl;
            }
            objectEnv.addid(curName,new Symbol (curType));
            localVarT[curName]=curType;
        }
        //check Main Params
        if(funcName==Main && vars->len()!=0){
            semant_error(this)<<"Main Function Should Not Have Params"<<endl;
        }
        if(funcName==Main && returnType!=Void){
            semant_error(this)<<"Main Function must be defined type Void"<<endl;
        }

        //check StmtBlock
        body->check(returnType);
        VariableDecls vars_in_Block=body->getVariableDecls();
        for(int i=vars_in_Block->first();vars_in_Block->more(i);i=vars_in_Block->next(i)){
            VariableDecl cur_decl=vars_in_Block->nth(i);
            cur_decl->check();
        }
        if(!body->isReturnStmt()){
            semant_error(this)<<"Function Should Have a Return Statement"<<endl;
        }
    }
    objectEnv.exitscope();
}

void StmtBlock_class::check(Symbol type) {
    VariableDecls vars=this->getVariableDecls();
    for(int i=vars->first();vars->more(i);i=vars->next(i)){
        VariableDecl var=vars->nth(i);
        var->check();
    }
    this->pass_single_stmt_flag();
    Stmts stmts=this->getStmts();

    for(int i=stmts->first();stmts->more(i);i=stmts->next(i)){
        Stmt cur_stmt=stmts->nth(i);
        cur_stmt->check(type);
    }
}

void IfStmt_class::check(Symbol type) {
    Expr condition=this->getCondition();
    StmtBlock stmtThen=this->getThen();
    StmtBlock stmtElse=this->getElse();

    Symbol conditionType=condition->checkType();
    if(conditionType!=Bool){
        semant_error(this)<<"Condition of If Statement should be Bool Type"<<endl;
    }
    stmtThen->setFlag(this->getLoopFlag());
    stmtThen->check(type);
    stmtElse->setFlag(this->getLoopFlag());
    stmtElse->check(type);
}

void WhileStmt_class::check(Symbol type) {
    Expr condition=this->getCondition();
    StmtBlock stmtBody=this->getBody();
    Symbol conditionType=condition->checkType();
    if(conditionType!=Bool){
        semant_error(this)<<"Condition of While Statement Should be Bool Type"<<endl;
    }
    stmtBody->setFlag(true);
    stmtBody->check(type);
}

void ForStmt_class::check(Symbol type) {
    Expr init=this->getInit();
    Expr condition=this->getCondition();
    Expr loopact=this->getLoop();
    StmtBlock stmtBody=this->getBody();
    stmtBody->setFlag(true);

    init->checkType();
    loopact->checkType();
    if(condition->is_empty_Expr()){
        stmtBody->check(type);
        return;
    }else{
        Symbol conditionType=condition->checkType();
        if(conditionType!=Bool){
            semant_error(this)<<"Condition Expression of For Statement Should be Bool Type"<<endl;
        }
        stmtBody->check(type);
    }
}

void ReturnStmt_class::check(Symbol type) {
    Expr value=this->getValue();
    if(value->is_empty_Expr()){
        if(type!=Void){
            semant_error(this)<<"Need a Return Value!"<<endl;
        }
    }else{
        Symbol valueType=value->checkType();
        if(valueType!=type){
            semant_error(this)<<"Return "<<valueType<<", but need "<<type<<endl;
        }
    }
}

void ContinueStmt_class::check(Symbol type) {
    if(!this->getLoopFlag()){
        semant_error(this)<<"Continue Statement Must be Used in Loop"<<endl;
    }
}

void BreakStmt_class::check(Symbol type) {
    if(!this->getLoopFlag()){
        semant_error(this)<<"Break Statement Muse be Used in Loop"<<endl;
    }
}

Symbol Call_class::checkType(){
    Symbol name=this->getName();
    Actuals actuals=this->getActuals();
    
    if(name==print){
        if(actuals->len()==0){
            semant_error(this)<<"function printf() should have at least one parameter"<<endl;
            this->setType(Void);
            return type;
        }
        Symbol paramType=actuals->nth(actuals->first())->checkType();
        if(paramType!=String){
            semant_error(this)<<"Function printf() Parameters Should be Type String"<<endl;
            this->setType(Void);
            return type;
        }
        this->setType(Void);
        return type;
    }
    int j=0;
    if(actuals->len()>0){
        if(actuals->len()!=int(actualParaT[name].size())){
            semant_error(this)<<"Wrong Number of Parameters"<<endl;
        }
        for(int i=actuals->first();actuals->more(i);i=actuals->next(i)){
            Expr expr=actuals->nth(i)->getExpr();
            Symbol exprType=expr->checkType();
            if(exprType==Void){
                semant_error(this)<<"Parameter type cannot be Void"<<endl;
            }
            if(exprType !=actualParaT[name][j]){
                semant_error(this)<<"Parameter has Wrong type"<<endl;
            }
            j++;
            actuals->nth(i)->checkType();
        }
    }
    if(funcT[name]==NULL){
        semant_error(this)<<"function "<<name<<"has not been declared"<<endl;
    }
    this->setType(funcT[name]);
    return type;
}

Symbol Actual_class::checkType(){
    Expr expr=this->getExpr();
    Symbol exprType=expr->checkType();
    this->setType(exprType);
    return type;
}

Symbol Assign_class::checkType(){
    Symbol lvalue=this->getlValue();
    Expr value=this->getValue();
    if(objectEnv.lookup(lvalue)==NULL && globalVarT[lvalue]==NULL){
        semant_error(this)<<"lvalue Undefined"<<endl;
    }
    Symbol ls=localVarT[lvalue];
    Symbol rs=value->checkType();
    
    if(ls!=rs){
        semant_error(this)<<"type of left value and right value should be the same"<<endl;
    }
    else{
        this->setType(rs);
        return type;
    }
}

Symbol Add_class::checkType(){
    Symbol ls=e1->checkType();
    Symbol rs=e2->checkType();
    //deal with default type exchange
    if(ls!=rs && !(ls==Int && rs==Float)&&!(ls==Float && rs==Int)){
        //unable to perform type exchange
        semant_error(this)<<"two expressions in add should have same type"<<endl;
    }
    else if((ls==Float && rs==Int)||(ls==Int && rs==Float)){
        this->setType(Float);
        return type;
    }else{
        this->setType(ls);
        return type;
    }
}

Symbol Minus_class::checkType(){
    Symbol ls=e1->checkType();
    Symbol rs=e2->checkType();
    //deal with default type exchange
    if(ls!=rs && !(ls==Int && rs==Float)&&!(ls==Float && rs==Int)){
        //unable to perform type exchange
        semant_error(this)<<"two expressions in minus should have same type"<<endl;
    }
    else if((ls==Float && rs==Int)||(ls==Int && rs==Float)){
        this->setType(Float);
        return type;
    }else{
        this->setType(ls);
        return type;
    }
}

Symbol Multi_class::checkType(){
    Symbol ls=e1->checkType();
    Symbol rs=e2->checkType();
    //deal with default type exchange
    if(ls!=rs && !(ls==Int && rs==Float)&&!(ls==Float && rs==Int)){
        //unable to perform type exchange
        semant_error(this)<<"two expressions in multi should have same type"<<endl;
    }
    else if((ls==Float && rs==Int)||(ls==Int && rs==Float)){
        this->setType(Float);
        return type;
    }else{
        this->setType(ls);
        return type;
    }
}

Symbol Divide_class::checkType(){
    Symbol ls=e1->checkType();
    Symbol rs=e2->checkType();
    //deal with default type exchange
    if(ls!=rs && !(ls==Int && rs==Float)&&!(ls==Float && rs==Int)){
        //unable to perform type exchange
        semant_error(this)<<"two expressions in divide should have same type"<<endl;
    }
    else if((ls==Float && rs==Int)||(ls==Int && rs==Float)){
        this->setType(Float);
        return type;
    }else{
        this->setType(ls);
        return type;
    }
}

Symbol Mod_class::checkType(){
    Symbol ls=e1->checkType();
    Symbol rs=e2->checkType();

    if(ls!=rs && !(ls==Int && rs==Float)&&!(ls==Float && rs==Int)){
        //unable to perform type exchange
        semant_error(this)<<"two expressions should in mod have same type"<<endl;
    }
    else if((ls==Float && rs==Int)||(ls==Int && rs==Float)){
        this->setType(Float);
        return type;
    }else{
        this->setType(ls);
        return type;
    }
}

Symbol Neg_class::checkType(){
    Expr e1=this->gete1();
    Symbol valueType=e1->checkType();
    if(valueType!=Int || valueType!=Float){
        semant_error(this)<<"TypeError"<<endl;
    }
    this->setType(valueType);
    return type;
}

Symbol Lt_class::checkType(){
    Symbol ls=e1->checkType();
    Symbol rs=e2->checkType();
    if((ls!=Int && ls!=Float)||(rs!=Int && rs!=Float)){
        semant_error(this)<<"Value Type should be Int or Float"<<endl;
    }
    this->setType(Bool);
    return type;
}

Symbol Le_class::checkType(){
    Symbol ls=e1->checkType();
    Symbol rs=e2->checkType();
    if((ls!=Int && ls!=Float)||(rs!=Int && rs!=Float)){
        semant_error(this)<<"Value Type should be Int or Float"<<endl;
    }
    this->setType(Bool);
    return type;
}

Symbol Equ_class::checkType(){
    Symbol ls=e1->checkType();
    Symbol rs=e2->checkType();
    if(((ls!=Int && ls!=Float)||(rs!=Int && rs!=Float))&&(ls!=Bool || rs!=Bool)){
        semant_error(this)<<"Bool equation calculation Type Error"<<endl;
    }
    this->setType(Bool);
    return type;
}

Symbol Neq_class::checkType(){
    Symbol ls=e1->checkType();
    Symbol rs=e2->checkType();
    if(((ls!=Int && ls!=Float)||(rs!=Int && rs!=Float))&&(ls!=Bool || rs!=Bool)){
        semant_error(this)<<"Bool Nonequation calculation Type Error"<<endl;
    }
    this->setType(Bool);
    return type;
}

Symbol Ge_class::checkType(){
    Symbol ls=e1->checkType();
    Symbol rs=e2->checkType();
    if((ls!=Int && ls!=Float)||(rs!=Int && rs!=Float)){
        semant_error(this)<<"Value Type should be Int or Float"<<endl;
    }
    this->setType(Bool);
    return type;
}

Symbol Gt_class::checkType(){
    Symbol ls=e1->checkType();
    Symbol rs=e2->checkType();
    if((ls!=Int && ls!=Float)||(rs!=Int && rs!=Float)){
        semant_error(this)<<"Value Type should be Int or Float"<<endl;
    }
    this->setType(Bool);
    return type;
}

Symbol And_class::checkType(){
    Symbol ls=e1->checkType();
    Symbol rs=e2->checkType();

    if(ls!=Bool || rs!=Bool){
        semant_error(this)<<"logical calc values should have type Bool"<<endl;
    }
    else{
        this->setType(Bool);
        return type;
    }
}

Symbol Or_class::checkType(){
    Symbol ls=e1->checkType();
    Symbol rs=e2->checkType();

    if(ls!=Bool || rs!=Bool){
        semant_error(this)<<"logical calc values should have type Bool"<<endl;
    }
    else{
        this->setType(Bool);
        return type;
    }
}

Symbol Xor_class::checkType(){
    Symbol ls=e1->checkType();
    Symbol rs=e2->checkType();
    if(!(ls==Bool && rs==Bool)&&!(ls==Int && rs==Int)){
        semant_error(this)<<"xor calculation wrong type!"<<endl;
    }
    else{
        this->setType(ls);
        return type;
    }
}

Symbol Not_class::checkType(){
    Symbol ls=e1->checkType();
    if(ls!=Bool){
        semant_error(this)<<"Not calc should have type Bool"<<endl;
    }else{
        this->setType(Bool);
        return type;
    }
}

Symbol Bitand_class::checkType(){
    Symbol ls=e1->checkType();
    Symbol rs=e2->checkType();

    if(!(ls==Int && rs==Int)){
        semant_error(this)<<"Bit calculation should have type Int"<<endl;
    }else{
        this->setType(Int);
        return type;
    }
}

Symbol Bitor_class::checkType(){
    Symbol ls=e1->checkType();
    Symbol rs=e2->checkType();

    if(!(ls==Int && rs==Int)){
        semant_error(this)<<"Bit calculation should have type Int"<<endl;
    }else{
        this->setType(Int);
        return type;
    }
}

Symbol Bitnot_class::checkType(){
    Symbol ls=e1->checkType();
    if(ls!=Int){
        semant_error(this)<<"Bit calculation should have type Int"<<endl;
    }else{
        this->setType(Int);
        return type;
    }
}

Symbol Const_int_class::checkType(){
    setType(Int);
    return type;
}

Symbol Const_string_class::checkType(){
    setType(String);
    return type;
}

Symbol Const_float_class::checkType(){
    setType(Float);
    return type;
}

Symbol Const_bool_class::checkType(){
    setType(Bool);
    return type;
}

Symbol Object_class::checkType(){
    if(objectEnv.lookup(var)==NULL){
        semant_error(this)<<"object "<<var<<" has not been defined"<<endl;
        this->setType(Void);
        return type;
    }
    Symbol vartype=localVarT[var];
    this->setType(vartype);
    return type;
}

Symbol No_expr_class::checkType(){
    setType(Void);
    return getType();
}

void Program_class::semant() {
    initialize_constants();
    install_calls(decls);
    check_main();
    install_globalVars(decls);
    check_calls(decls);
    
    if (semant_errors > 0) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }
}



