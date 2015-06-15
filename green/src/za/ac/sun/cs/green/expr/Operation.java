package za.ac.sun.cs.green.expr;

import java.math.BigInteger;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Set;

import za.ac.sun.cs.green.expr.Operation.Operator;

public class Operation extends Expression {

	public static enum Fix {
		PREFIX, INFIX, POSTFIX;
	}

	public static enum Operator {
		// Logical Operations
		EQ("==", 2, Fix.INFIX, true),
		NE("!=", 2, Fix.INFIX, true),
		LT("<", 2, Fix.INFIX, true),
		LE("<=", 2, Fix.INFIX, true),
		GT(">", 2, Fix.INFIX, true),
		GE(">=", 2, Fix.INFIX, true),
		AND("&&", 2, Fix.INFIX, true),
		OR("||", 2, Fix.INFIX, true),
		IMPLIES("=>", 2, Fix.INFIX, true),
		NOT("!", 1, Fix.INFIX, true),
		
		// Basic Arithmetic Operations
		ADD("+", 2, Fix.INFIX),
		SUB("-", 2, Fix.INFIX),
		MUL("*", 2, Fix.INFIX),
		DIV("/", 2, Fix.INFIX),
		MOD("%", 2, Fix.INFIX),
		NEG("-", 1, Fix.INFIX),

		// Complex Arithmetic Operations
		SIN("SIN", 1),
		COS("COS", 1),
		TAN("TAN", 1),
		ASIN("ASIN", 1),
		ACOS("ACOS", 1),
		ATAN("ATAN", 1),
		ATAN2("ATAN2", 2),
		ROUND("ROUND", 1),
		LOG("LOG", 1),
		EXP("EXP", 1),
		POWER("POWER", 1),
		SQRT("SQRT", 1),
		
		// String Operations
		SUBSTRING("SUBSTRING", 3, Fix.POSTFIX),
		CONCAT("CONCAT", 2, Fix.POSTFIX),
		TRIM("TRIM", 1, Fix.POSTFIX), 
		REPLACE("REPLACE", 3, Fix.POSTFIX),
		REPLACEFIRST("REPLACEFIRST", 3, Fix.POSTFIX),  
		TOLOWERCASE("TOLOWERCASE", 2, Fix.POSTFIX),
		TOUPPERCASE("TOUPPERCASE", 2, Fix.POSTFIX), 
		VALUEOF("VALUEOF", 2, Fix.POSTFIX),
		
		// String Comparators
		NOTCONTAINS("NOTCONTAINS", 2, Fix.POSTFIX, true),
		CONTAINS("CONTAINS", 2, Fix.POSTFIX, true),
		LASTINDEXOFCHAR("LASTINDEXOFCHAR", 3, Fix.POSTFIX),
		LASTINDEXOFSTRING("LASTINDEXOFSTRING", 3, Fix.POSTFIX),
		STARTSWITH("STARTSWITH", 3, Fix.POSTFIX, true),
		NOTSTARTSWITH("NOTSTARTSWITH", 3, Fix.POSTFIX, true),
		ENDSWITH("ENDSWITH", 2, Fix.POSTFIX, true),
		NOTENDSWITH("NOTENDSWITH", 2, Fix.POSTFIX, true),
		STRINGEQUALS("STRINGEQUALS", 2, Fix.POSTFIX, true),
		STRINGNOTEQUALS("STRINGNOTEQUALS", 2, Fix.POSTFIX, true),
		EQUALSIGNORECASE("EQUALSIGNORECASE", 2, Fix.POSTFIX, true),
		NOTEQUALSIGNORECASE("NOTEQUALSIGNORECASE", 2, Fix.POSTFIX, true),
		EMPTY("EMPTY", 1, Fix.POSTFIX, true),
		NOTEMPTY("NOTEMPTY", 1, Fix.POSTFIX, true),
		ISINTEGER("ISINTEGER", 1, Fix.POSTFIX, true),
		NOTINTEGER("NOTINTEGER", 1, Fix.POSTFIX, true),
		ISFLOAT("ISFLOAT", 1, Fix.POSTFIX, true),
		NOTFLOAT("NOTFLOAT", 1, Fix.POSTFIX, true),
		ISLONG("ISLONG", 1, Fix.POSTFIX, true),
		NOTLONG("NOTLONG", 1, Fix.POSTFIX, true),
		ISDOUBLE("ISDOUBLE", 1, Fix.POSTFIX, true),
		NOTDOUBLE("NOTDOUBLE", 1, Fix.POSTFIX, true),
		ISBOOLEAN("ISBOOLEAN", 1, Fix.POSTFIX, true),
		NOTBOOLEAN("NOTBOOLEAN", 1, Fix.POSTFIX, true),
		REGIONMATCHES("REGIONMATCHES", 6, Fix.POSTFIX, true),
		NOTREGIONMATCHES("NOTREGIONMATCHES", 6, Fix.POSTFIX, true),
		
		// Full set of BitVector operations (from http://smtlib.cs.uiowa.edu/logics/QF_BV.smt2)
		BVCONCAT("CONCAT", 2, Fix.PREFIX),
		BVEXTRACT("EXTRACT", 3, Fix.PREFIX), // First two params index the extract function, third is bv value
		ITE("ITE", 3, Fix.PREFIX),
		BVNOT("~", 1, Fix.PREFIX),
		BVAND("&", 2, Fix.INFIX),
		BVOR("|", 2, Fix.INFIX),
		BVNEG("BVNEG", 1),
		BVADD("BVADD", 2, Fix.PREFIX),
		BVMUL("BVMUL", 2, Fix.PREFIX),
		BVUDIV("BVUDIV", 2, Fix.PREFIX),
		BVUREM("BVUREM", 2, Fix.PREFIX),
		BVSHL("<<", 2, Fix.INFIX),
		BVLSHR(">>>", 2, Fix.INFIX),
		BVULT("BVULT", 2, Fix.PREFIX, true),
		
		// The following operations can be rewritten (and simplified) by the canonizer
		BVNAND("BVNAND", 2, Fix.PREFIX), // Desugar to : BVNOT(BVAND(...))
		BVNOR("BVNOR", 2, Fix.PREFIX), // Desugar to : BVNOT(BVOR(...))
		BVXOR("^", 2, Fix.INFIX), // Desugar to : BVOR(BVAND(#1,BVNOT(#2)), BVAND(BVNOT(#1),#2))
		BVXNOR("BVXNOR", 2, Fix.PREFIX), // Desugar to : BVOR(BVAND(#1,#2), BVAND(BVNOT(#1),BVNOT(#2)))
		BVCOMP("BVCOMP", 2, Fix.PREFIX), // Desugar to ... see QF_BV definition
		BVSUB("BVSUB", 2, Fix.PREFIX), // Desugar to : BVADD(#1,BVNEG(#2))
		BVSDIV("BVSDIV", 2, Fix.PREFIX), // Desugar to ... see QF_BV definition
		BVSREM("BVSREM", 2, Fix.PREFIX), // Desugar to ... see QF_BV definition
		BVSMOD("BVSMOD", 2, Fix.PREFIX), // Desugar to ... see QF_BV definition
		BVASHR(">>", 2, Fix.INFIX), // Desugar to ... see QF_BV definition
		BVREPEAT("RPT", 2, Fix.PREFIX), // Desugar to ... see QF_BV definition
		BVZEROEXTEND("ZEXT", 2, Fix.PREFIX), // Desugar to ... see QF_BV definition
		BVSIGNEXTEND("SEXT", 2, Fix.PREFIX), // Desugar to ... see QF_BV definition
		BVROTATELEFT("ROTL", 2, Fix.PREFIX), // Desugar to ... see QF_BV definition
		BVROTATERIGHT("ROTR", 2, Fix.PREFIX), // Desugar to ... see QF_BV definition
		BVULE("BVULE", 2, Fix.PREFIX, true), // Desugar to : OR(BVULT(#1,#2),#1==#2)
		BVUGT("BVUGT", 2, Fix.PREFIX, true), // Desugar to : BVULT(#2,#1)
		BVUGE("BVUGE", 2, Fix.PREFIX, true), // Desugar to : OR(BVULT(#2,#1),#1==#2)
		BVSLT("BVSLT", 2, Fix.PREFIX, true), // Desugar to ... see QF_BV definition
		BVSLE("BVSLE", 2, Fix.PREFIX, true), // Desugar to ... see QF_BV definition
		BVSGT("BVSGT", 2, Fix.PREFIX, true), // Desugar to : BVSLT(#2,#1)
		BVSGE("BVSGE", 2, Fix.PREFIX, true), // Desugar to : BVSLE(#2,#1)
		
		
		//Eric's new ones
		BVLSHL("BVLSHL", 2, Fix.PREFIX),
		
		// Array operations
		STORE("STORE", 3, Fix.PREFIX),
		
		/*
		 * This is a change from matt.  Basically here you are asserting
		 * 
		 * 1) What array it's coming from
		 * 2) What element of that array (Perhaps constant, perhaps some operation)
		 */
		SELECT("SELECT", 2, Fix.PREFIX);

		private final String string;

		private final int maxArity;

		private final Fix fix;
		
        private final boolean comparator;
        
        private static final Set<Operation.Operator> commutes;
        static {
        		Set<Operation.Operator> tmp = new HashSet<Operation.Operator>();
        		tmp.add(Operation.Operator.EQ);
        		tmp.add(Operation.Operator.NE);
        		tmp.add(Operation.Operator.AND);
        		tmp.add(Operation.Operator.OR);
        		tmp.add(Operation.Operator.ADD);
        		tmp.add(Operation.Operator.MUL);
        		tmp.add(Operation.Operator.BVAND);
        		tmp.add(Operation.Operator.BVOR);
        		tmp.add(Operation.Operator.BVADD);
        		tmp.add(Operation.Operator.BVMUL);
        		tmp.add(Operation.Operator.BVNAND);
        		tmp.add(Operation.Operator.BVNOR);
        		tmp.add(Operation.Operator.BVXOR);
        		tmp.add(Operation.Operator.BVXNOR);
        		commutes = Collections.unmodifiableSet(tmp);
        }

        Operator(String string, int maxArity) {
                this.string = string;
                this.maxArity = maxArity;
                this.fix = Fix.PREFIX;
                this.comparator = false;
        }

        Operator(String string, int maxArity, Fix fix) {
                this.string = string;
                this.maxArity = maxArity;
                this.fix = fix;
                this.comparator = false;
        }

        Operator(String string, int maxArity, Fix fix, boolean comparator){
                this.string = string;
                this.maxArity = maxArity;
                this.fix = fix;
                this.comparator = comparator;
        }

        @Override
        public String toString() {
                return string;
        }

        public int getArity() {
                return maxArity;
        }

        public Fix getFix() {
                return fix;
        }

        public boolean isComparator(){
                return comparator;
        }
        
        public static boolean isCommutative(Operation.Operator op) {
        		return commutes.contains(op);
        }

	}

	public static final BitVectorConstant BV_ZERO = new BitVectorConstant(new BigInteger("0"), 32);

	public static final BitVectorConstant BV_ONE = new BitVectorConstant(new BigInteger("1"), 32);

	public static final Operation BV_FALSE = new Operation(Operation.Operator.EQ, BV_ZERO, BV_ONE);

	public static final Operation BV_TRUE = new Operation(Operation.Operator.EQ, BV_ZERO, BV_ZERO);
	
	
	
	public static final IntConstant LI_ZERO = new IntConstant(0);

	public static final IntConstant LI_ONE = new IntConstant(1);

	public static final Operation LI_FALSE = new Operation(Operation.Operator.EQ, LI_ZERO, LI_ONE);

	public static final Operation LI_TRUE = new Operation(Operation.Operator.EQ, LI_ZERO, LI_ZERO);
	
	private final Operator operator;

	private final Expression[] operands;
	
	private StringBuilder string;
	
	private int stringStart;
	
	private int stringStop;
	
	private boolean stringBuilt;
	
	private int hashCode;
	
	private boolean hashCodeBuilt;

	public Operation(final Operator operator, Expression... operands) {
		this.operator = operator;
		this.operands = operands;

		this.hashCodeBuilt = false;
		this.stringBuilt = false;
		
		this.hashCode = 0;
		
		this.stringStart = 0;
		this.stringStop = 0;
		this.string = null;
	}

	public Operator getOperator() {
		return operator;
	}

	public Iterable<Expression> getOperands() {
		return new Iterable<Expression>() {
			@Override
			public Iterator<Expression> iterator() {
				return new Iterator<Expression>() {
					private int index = 0;

					@Override
					public boolean hasNext() {
						return index < operands.length;
					}

					@Override
					public Expression next() {
						if (index < operands.length) {
							return operands[index++];
						} else {
							throw new NoSuchElementException();
						}
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
				};
			}
		};
	}

	public Expression getOperand(int index) {
		if ((index < 0) || (index >= operands.length)) {
			return null;
		} else {
			return operands[index];
		}
	}

	@Override
	public void accept(Visitor visitor) throws VisitorException {
		visitor.preVisit(this);
		for (Expression operand : operands) {
			operand.accept(visitor);
		}
		visitor.postVisit(this);
	}

//	@Override
//	public int compareTo(Expression expression) {
//		Operation operation = (Operation) expression;
//		int result = operator.compareTo(operation.operator);
//		if (result != 0) {
//			return result;
//		}
//		if (operands.length < operation.operands.length) {
//			return -1;
//		} else if (operands.length > operation.operands.length) {
//			return 1;
//		}
//		for (int i = 0; i < operands.length; i++) {
//			result = operands[i].compareTo(operation.operands[i]);
//			if (result != 0) {
//				return result;
//			}
//		}
//		return 0;
//	}

	@Override
	public boolean equals(Object object) {
		if (object instanceof Operation) {
			Operation operation = (Operation) object;
			if (operator != operation.operator) {
				return false;
			}
			if (operands.length != operation.operands.length) {
				return false;
			}
			for (int i = 0; i < operands.length; i++) {
				if (!operands[i].equals(operation.operands[i])) {
					return false;
				}
			}
			return true;
		} else {
			return false;
		}
	}

	@Override
	public int hashCode(){
		if(!hashCodeBuilt){
			hashCode = hashCodeBuild();
			hashCodeBuilt = true;
		}
		return hashCode;
	}
	
	public int hashCodeBuild() {
		return this.toString().hashCode();
	}

	@Override	
	public String toString(){
		if(!stringBuilt){
//			System.out.println("\n\n\n\nBuilding completely new");
			toStringBuild(new StringBuilder());
//			System.out.println("Done Building Completely new\n\n\n\n");
		}
		return string.substring(stringStart, stringStop);
	}
	
	private void stringDecider(Expression e, StringBuilder sb){
		if(e instanceof Operation){
			((Operation)e).toStringBuild(sb);
		}else {
			sb.append(e.toString());
		}
	}

	private void toStringBuild(StringBuilder sb) {
		if(stringBuilt){
			sb.append(string.substring(stringStart, stringStop));
		}else{
//			System.out.println("Building: "+this.operator.toString());
			this.string = sb;
			this.stringStart=sb.length();

			int arity = operator.getArity();
			Fix fix = operator.getFix();
			if (arity == 2 && fix == Fix.INFIX) {
				if ((operands[0] instanceof Constant) || (operands[0] instanceof Variable)) {
					sb.append(operands[0].toString());
				} else {
					sb.append('(');
					stringDecider(operands[0], sb);
					sb.append(')');
				}
				sb.append(operator.toString());
				if ((operands[1] instanceof Constant) || (operands[1] instanceof Variable)) {
					sb.append(operands[1].toString());
				} else {
					sb.append('(');
					stringDecider(operands[1], sb);
					sb.append(')');
				}
			} else if (arity == 1 && fix == Fix.INFIX) {
				sb.append(operator.toString());
				if ((operands[0] instanceof Constant) || (operands[0] instanceof Variable)) {
					sb.append(operands[0].toString());
				} else {
					sb.append('(');
					stringDecider(operands[0], sb);
					sb.append(')');
				}
			} else if (fix == Fix.POSTFIX) {
				stringDecider(operands[0], sb);
				sb.append('.');
				sb.append(operator.toString());
				sb.append('(');
				if (operands.length > 1) {
					stringDecider(operands[1], sb);
					for (int i = 2; i < operands.length; i++) {
						sb.append(',');
						stringDecider(operands[i], sb);
					}
				}
				sb.append(')');
			} else if (operands.length > 0) {
				sb.append(operator.toString());
				sb.append('(');
				stringDecider(operands[0], sb);
				for (int i = 1; i < operands.length; i++) {
					if(operands[i]!=null){
						sb.append(',');
						stringDecider(operands[i], sb);
					}
				}
				sb.append(')');
			} else {
				sb.append(operator.toString());
			}

			this.stringStop = sb.length();
			this.stringBuilt = true;
		}
	}

	/*
	 * For memory purposes
	 */
	public void clearString() {
		string = null;
		stringBuilt = false;
		
	}

}
