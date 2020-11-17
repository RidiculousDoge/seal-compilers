 /*
  *  The scanner definition for seal.
  */

 /*
  *  Stuff enclosed in %{ %} in the first section is copied verbatim to the
  *  output, so headers and global definitions are placed here to be visible
  * to the code in the file.  Don't remove anything that was here initially
  */

  /*
  to do list
  1. exchange const-int: 0x to tenth
  2. process string overflow
  3. add symbols used to symbol table(FINISHED!)
  4. process chars with "\"
  */
%{

#include <seal-parse.h>
#include <stringtab.h>
#include <utilities.h>
#include <stdint.h>
#include <stdlib.h>

/* The compiler assumes these identifiers. */
#define yylval seal_yylval
#define yylex  seal_yylex

/* Max size of string constants */
#define MAX_STR_CONST 256
#define YY_NO_UNPUT   /* keep g++ happy */
#define MAX_DEC_CONST 20

extern FILE *fin; /* we read from this file */

/* define YY_INPUT so we read from the FILE fin:
 * This change makes it possible to use this scanner in
 * the seal compiler.
 */
#undef YY_INPUT
#define YY_INPUT(buf,result,max_size) \
	if ( (result = fread( (char*)buf, sizeof(char), max_size, fin)) < 0) \
		YY_FATAL_ERROR( "read() in flex scanner failed");

char string_buf[MAX_STR_CONST]; /* to assemble string constants */
char *string_buf_ptr;
int string_const_len;
bool str_contain_null_char;
int hex_val;

int raw_string_const_len;
bool raw_str_contain_null_char;
char raw_string_buf[MAX_STR_CONST];

extern int curr_lineno;
extern int verbose_flag;

extern YYSTYPE seal_yylval;
static int comment_layer=0;

/*
 *  Add Your own definitions here
 */
 


%}
%option noyywrap

%x    COMMENT
%x    IFILE
%x    STRING
%x    RAW_STRING    
 /*
  * Define names for regular expressions here.
  */

%%

true  {
  seal_yylval.boolean=1;
  return (CONST_BOOL);
}
false {
  seal_yylval.boolean=0;
  return(CONST_BOOL);
}

Int|Float|Bool|String|Void  {
    printf("#%d TYPEID %s\n",curr_lineno,yytext);
}

(?:var)   { return (VAR);}

(?:func)  { return (FUNC);}

(?:if)    { return (IF);}

(?:else)  { return (ELSE);}

(?:while) { return (WHILE);}

(?:for)   { return (FOR);}

(?:break) { return (BREAK);}

(?:continue)  { return (CONTINUE);}

(?:return)    { return (RETURN);}

(?:struct)    { return (STRUCT);}


[a-z][A-Za-z0-9_]*    {
  seal_yylval.symbol=idtable.add_string(yytext);
  return (OBJECTID);
}

[0-9]+    {
  seal_yylval.symbol=inttable.add_string(yytext);
  return (CONST_INT);
}

[0-9]+"."[0-9]+   {
  seal_yylval.symbol=floattable.add_string(yytext);
  return (CONST_FLOAT);
}

0[xX][1-9a-fA-F]+   {
  hex_val=0;
  int times=0;
  for(int i=yyleng-1;i>1;i--){
    if(times==0) times=1;
    else times*=16;
    if(yytext[i]-'0'>=0 && yytext[i]-'9'<=0){
      hex_val+=(yytext[i]-'0')*times;
    }
    else{
      if(yytext[i]-'a'>=0 && yytext[i]-'f'<=0)
        hex_val+=(yytext[i]-'a'+10)*times;
      else if(yytext[i]-'A'>=0 && yytext[i]-'F'<=0)
        hex_val+=(yytext[i]-'A'+10)*times;
    }
  }
  char dec_string[MAX_DEC_CONST]={0};
  sprintf(dec_string,"%d",hex_val);
  seal_yylval.symbol=inttable.add_string(dec_string);
  return (CONST_INT);
}

[ \f\r\t\v]+ { }

"/*"            {BEGIN(COMMENT);}

<COMMENT>"*/"   {BEGIN(INITIAL);}

<COMMENT>\n   {
  curr_lineno++;
}

<COMMENT>([^*\n])+|.   {}

<COMMENT><<EOF>>  {
  strcpy(seal_yylval.error_msg,"EOF in comment");
  BEGIN(INITIAL);
  return (ERROR);
}

"\""  {
  memset(string_buf,0,sizeof string_buf);
  string_const_len=0;
  str_contain_null_char=false;
  BEGIN (STRING);
}
<STRING>\\\n  {
  curr_lineno++;
  string_buf[string_const_len++]='\n';
}

<STRING>\n  {
  curr_lineno++;
  strcpy(seal_yylval.error_msg,"Unterminated string constant");
  BEGIN(INITIAL);
  return (ERROR);
}


<STRING>\\. {
  if(string_const_len>=MAX_STR_CONST){
    strcpy(seal_yylval.error_msg,"String constant too long!");
    BEGIN(INITIAL);
    return (ERROR);
  }
  switch(yytext[1]){
    case 'b': string_buf[string_const_len++] = '\b'; break;
    case 'f': string_buf[string_const_len++] = '\f'; break;
    case 'n': string_buf[string_const_len++] = '\n'; break;
    case 't': string_buf[string_const_len++] = '\t'; break;
    case '0': string_buf[string_const_len++] = 0;
              str_contain_null_char=true;
              break;
    default: string_buf[string_const_len++]=yytext[1];
  }
}

<STRING>\" {
  if(string_const_len>1 && str_contain_null_char){
    strcpy(seal_yylval.error_msg,"String contains null character '\\0'");
    BEGIN(INITIAL);
    return (ERROR);
  }
  seal_yylval.symbol=stringtable.add_string(string_buf);
  BEGIN(INITIAL);
  return (CONST_STRING);
}

<STRING>. {
  if(string_const_len>=MAX_STR_CONST){
    strcpy(seal_yylval.error_msg,"String constant too long!");
    BEGIN(INITIAL);
    return (ERROR);
  }
  string_buf[string_const_len++]=yytext[0];
}

<STRING><<EOF>> {
  strcpy(seal_yylval.error_msg,"EOF in string constant");
  BEGIN (INITIAL);
  return (ERROR);
}

"`"  {
  memset(raw_string_buf,0,sizeof raw_string_buf);
  raw_string_const_len=0;
  raw_str_contain_null_char=false;
  BEGIN (RAW_STRING);
}
<RAW_STRING>\n  {
  curr_lineno++;
  raw_string_buf[raw_string_const_len++]='\n';
}

<RAW_STRING>` {
  seal_yylval.symbol=stringtable.add_string(raw_string_buf);
  BEGIN(INITIAL);
  return (CONST_STRING);
}

<RAW_STRING>. {
  if(raw_string_const_len>=MAX_STR_CONST){
    strcpy(seal_yylval.error_msg,"String constant too long!");
    BEGIN(INITIAL);
    return (ERROR);
  }
  raw_string_buf[raw_string_const_len++]=yytext[0];
}

<RAW_STRING><<EOF>> {
  strcpy(seal_yylval.error_msg,"EOF in string constant");
  BEGIN (INITIAL);
  return (ERROR);
}

"//".*\n    {}

"+"     {return '+';}

"-"     {return '-';}

"\*"    {return '*';}

"/"     {return '/';}

"<"     { return '<'; }

">"     { return '>';}

"="     { return '='; }

"."     { return '.'; }

";"     { return ';'; }

"~"     { return '~'; }

":"     { return ':'; }

","     { return ','; }

"%"     { return '%';}

"&"     { return '&';}

"^"     { return '^';}

"~"     { return '~';}

"!"     { return '!';}

"\|"    { return '|';}

">="    { return (GE);}

"!="    { return (NE);}

"<="    { return (LE);}

"=="    { return (EQUAL);}

"&&"    { return (AND);}

"||"    { return (OR);}

""

"\n" {
  curr_lineno++;
}

"{"     {return '{';}

"}"     {return '}';}

"("     {return '(';}

")"     {return ')';}

.	{
	strcpy(seal_yylval.error_msg, yytext); 
	return (ERROR); 
}

%%
