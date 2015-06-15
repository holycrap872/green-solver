// Define a grammar called SMT
grammar SMT;

/*
*Main Rule
*/
root: '(set-logic QF_AUFBV )' declarations assertions '(check-sat)' '(exit)';

/*
*Run through declarations
*/
declarations: ('(' DECLARE symbol '()' arrayDeclaration')')*;

arrayDeclaration: '(Array' arraySize arraySize ')';
arraySize: '(_ BitVec' NUMERAL ')';

/*
*
*/
assertions: ('(assert' expr ')')+;

expr: '(' ( nothing | single | doub | triple | bvnumber) ')' | symbol | bool;

triple : TRIPLE expr expr expr;
doub : DOUB expr expr;
single : SINGLE expr | let;
nothing: expr | bitManipulation expr;

let: 'let' '(' (letexpr)+ ')' expr;
letexpr: '(' SYMBOL expr ')';

SINGLE: 'empty';

DOUB: '=' | 'concat' | 'and' | 'or' | 'bvslt' | 'bvult' | 'bvsle' | 'bvule' | 'bvsgt' | 'bvugt' | 'bvsge' | 'bvuge' | 'bvadd' | 'bvsub' | 'bvmul' | 'bvudiv' | 'bvshl' | 'bvlshl' | 'bvshr' | 'bvlshr' | 'bvand' | 'bvnand' | 'bvor' | 'bvnor' | 'bvxor' | 'bvxnor' | 'select';

//select: 'select' (SYMBOL|'(' store ')'| '(' select ')') expr;
//store: 'store' (SYMBOL| '(' store ')' | '(' select ')') expr expr;

TRIPLE: 'ite' | 'store';

bitManipulation: EXTEND NUMERAL ')' | EXTRACT NUMERAL NUMERAL ')';
bvnumber: '_ bv' NUMERAL NUMERAL;


WS : [ \t\r\n]+ -> skip ; // skip spaces, tabs, newlines, \r (Windows)

/*
*Reserved Words
*/
ASSERT: 'assert';
DECLARE: 'declare-fun';
EXTEND: '(_ zero_extend' | '(_ sign_extend';
EXTRACT: '(_ extract';

bool: BOOLEAN;
BOOLEAN: 'true' | 'false';
BINARY: '#b'('0'|'1')+;
HEX:'#x'(('a'..'f')|('0'..'9')|('A'..'F'))+;
NUMERAL: ('0'..'9') | (('1'..'9')('0'..'9')+);

symbol: SYMBOL;
SYMBOL: SIMPLESYMBOL|QUOTEDSYMBOL;
SIMPLESYMBOL: SIMPLESYMBOLSTART(SIMPLESYMBOLFINISH)*;
SIMPLESYMBOLSTART: ('a'..'z')|('A'..'Z')| '~' | '!' | '@' | '$' | '%' | '^' | '&' | '*' | '_' | '+' | '=' | '<' | '>' | '.' | '?' | '/' | '-';
SIMPLESYMBOLFINISH: ('a'..'z') | ('A'..'Z') | ('0'..'9') | '~' | '!' | '@' | '$' | '%' | '^' | '&' | '*' | '_' | '+' | '=' | '<' | '>' | '.' | '?' | '/' | '-';
QUOTEDSYMBOL: '|a|';


