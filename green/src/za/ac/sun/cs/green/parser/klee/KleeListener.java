package za.ac.sun.cs.green.parser.klee;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.NotNull;
import org.antlr.v4.runtime.tree.ErrorNode;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.ParseTreeWalker;
import org.antlr.v4.runtime.tree.TerminalNode;

import za.ac.sun.cs.green.expr.Alias;
import za.ac.sun.cs.green.expr.ArrayVariable;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Operation.Operator;
import za.ac.sun.cs.green.expr.BitVectorConstant;
import antlr.SMTListener;
import antlr.SMTParser.ArrayDeclarationContext;
import antlr.SMTParser.ArraySizeContext;
import antlr.SMTParser.AssertionsContext;
import antlr.SMTParser.BitManipulationContext;
import antlr.SMTParser.BoolContext;
import antlr.SMTParser.BvnumberContext;
import antlr.SMTParser.DeclarationsContext;
import antlr.SMTParser.DoubContext;
import antlr.SMTParser.ExprContext;
import antlr.SMTParser.LetContext;
import antlr.SMTParser.LetexprContext;
import antlr.SMTParser.NothingContext;
import antlr.SMTParser.RootContext;
import antlr.SMTParser.SingleContext;
import antlr.SMTParser.SymbolContext;
import antlr.SMTParser.TripleContext;


public class KleeListener implements SMTListener{

	private Map<String, Expression> letMap;
	private Stack<Expression> s;
	private Expression returnExpression;
	private ParseTree tree;
	private Map<String, ArrayVariable> avMap;

	public KleeListener(ParseTree tree){
		letMap = new HashMap<String, Expression>();
		s = new Stack<Expression>();
		returnExpression = null;
		this.tree = tree;
		avMap = new HashMap<String, ArrayVariable>();
	}

	public Expression getExpression(){
		try{
			if(returnExpression == null){
				KleeParseTreeWalker ptw = new KleeParseTreeWalker();
				ptw.walk(this, tree);
				returnExpression = s.pop();
				//Add the initial declarations of the arrays
				while(!s.isEmpty()){
					Expression holder = s.pop();
					
					if(holder instanceof Operation && ((Operation)holder).getOperator().equals(Operation.Operator.EQ)){
						if(zeroArray((Operation)holder)){
//							continue;
						}
					}
					
					returnExpression = new Operation(Operation.Operator.AND, holder, returnExpression);
				}
				assert s.isEmpty();
			}
			return returnExpression;
		}catch(java.lang.Exception e){
			return null;
		}
	}

	private boolean zeroArray(Operation holder) {
		if(!(holder.getOperand(0) instanceof Operation)){
			return false;
		}
		Operation holdOp = (Operation)holder.getOperand(0);
		if(!(holdOp.getOperator().equals(Operation.Operator.SELECT))){
			return false;
		}
		
		
		if(!(holder.getOperand(1) instanceof BitVectorConstant)){
			return false;
		}
		BitVectorConstant con = (BitVectorConstant)holder.getOperand(1);
		if(!(con.getValue().equals(new BigInteger("0")))){
			return false;
		}
		
		if(!(holdOp.getOperand(0) instanceof ArrayVariable)){
			return false;
		}
		
		if(!(holdOp.getOperand(1) instanceof BitVectorConstant)){
			return false;
		}
		
		return true;
	}

	@Override
	public void enterEveryRule(@NotNull ParserRuleContext arg0) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void exitEveryRule(@NotNull ParserRuleContext arg0) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitErrorNode(@NotNull ErrorNode arg0) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitTerminal(@NotNull TerminalNode arg0) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void enterDoub(@NotNull DoubContext ctx) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void exitDoub(@NotNull DoubContext ctx) {
		String op = ctx.getChild(0).toString();
		if(op.equals("and")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.AND, l, r));
		}else if(op.equals("concat")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.CONCAT, l, r));
		}else if(op.equals("select")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.SELECT, l, r));
		}else if(op.equals("or")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.OR, l, r));
		}else if(op.equals("=")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.EQ, l, r));
		}else if(op.equals("bvslt")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.BVSLT, l, r));
		}else if(op.equals("bvult")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.BVULT, l, r));
		}else if(op.equals("bvsle")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.BVSLE, l, r));
		}else if(op.equals("bvule")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.BVULE, l, r));
		}else if(op.equals("bvsgt")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.BVSGT, l, r));
		}else if(op.equals("bvugt")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.BVUGT, l, r));
		}else if(op.equals("bvsge")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.BVSGE, l, r));
		}else if(op.equals("bvuge")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.BVUGE, l, r));
		}else if(op.equals("bvadd")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.BVADD, l, r));
		}else if(op.equals("bvsub")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.BVSUB, l, r));
		}else if(op.equals("bvmul")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.BVMUL, l, r));
		}else if(op.equals("bvudiv")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.BVUDIV, l, r));
		}else if(op.equals("bvshl")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.BVSHL, l, r));
		}else if(op.equals("bvlshl")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.BVLSHL, l, r));
		}else if(op.equals("bvshr")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.BVASHR, l, r));
		}else if(op.equals("bvlshr")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.BVLSHR, l, r));
		}else if(op.equals("bvand")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.BVAND, l, r));
		}else if(op.equals("bvnand")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.BVNAND, l, r));
		}else if(op.equals("bvor")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.BVOR, l, r));
		}else if(op.equals("bvnor")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.BVNOR, l, r));
		}else if(op.equals("bvxor")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.BVXOR, l, r));
		}else if(op.equals("bvxnor")){
			Expression r = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.BVXNOR, l, r));
		}else{
			Exception e = new Exception();
			System.out.println("Alleged operation: "+ op);
			e.printStackTrace();
			System.exit(1);
		}
	}

	@Override
	public void enterSingle(@NotNull SingleContext ctx) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void exitSingle(@NotNull SingleContext ctx) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void enterSymbol(@NotNull SymbolContext ctx) {
		// TODO Auto-generated method stub

	}

	@Override
	public void exitSymbol(@NotNull SymbolContext ctx) {
		String symbol = ctx.getChild(0).toString();
		if(letMap.containsKey(symbol)){
			if(!symbol.contains("?")){
				Exception e = new Exception();
				System.out.println("Alleged symbol: "+ symbol);
				e.printStackTrace();
				System.exit(1);
			}
			Expression e = letMap.get(symbol);
			s.push(e);
		}else{
			ArrayVariable av = avMap.get(symbol);
			if(av == null){
				av = new ArrayVariable(symbol);
				avMap.put(symbol, av);
			}
			s.push(av);
			if(symbol.contains(")")||symbol.contains("(")||
					symbol.contains("bv")||symbol.contains("true")||
					symbol.contains("false")||symbol.contains("let")||
					symbol.contains("store")||symbol.contains("and")||
					symbol.contains("select") || symbol.contains("concat") ||
					symbol.contains("=")){
				Exception e = new Exception();
				System.out.println("Alleged symbol: "+ symbol);
				e.printStackTrace();
				System.exit(1);
			}
		}
	}

	@Override
	public void enterArrayDeclaration(@NotNull ArrayDeclarationContext ctx) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void exitArrayDeclaration(@NotNull ArrayDeclarationContext ctx) {
//		System.out.println("here");
		IntConstant mem = (IntConstant)s.pop();
		IntConstant index = (IntConstant)s.pop();
		ArrayVariable av = (ArrayVariable)s.pop();
//		System.out.println(av.toString());
		av.setArrayDeclarations(index, mem);
	}

	@Override
	public void enterRoot(@NotNull RootContext ctx) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void exitRoot(@NotNull RootContext ctx) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void enterLet(@NotNull LetContext ctx) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void exitLet(@NotNull LetContext ctx) {
		// TODO Auto-generated method stub
		
	}


	@Override
	public void enterTriple(@NotNull TripleContext ctx) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void exitTriple(@NotNull TripleContext ctx) {
		String op = ctx.getChild(0).toString();
		if(op.equals("store")){
			Expression r = s.pop();
			Expression m = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.STORE, l, m, r));
		}else if(op.equals("ite")){
			Expression r = s.pop();
			Expression m = s.pop();
			Expression l = s.pop();
			s.push(new Operation(Operation.Operator.ITE, l, m, r));
		}else{
			Exception e = new Exception();
			System.out.println("Alleged operation: "+ op);
			e.printStackTrace();
			System.exit(1);
		}
	}

	@Override
	public void enterExpr(@NotNull ExprContext ctx) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void exitExpr(@NotNull ExprContext ctx) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void enterLetexpr(@NotNull LetexprContext ctx) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void exitLetexpr(@NotNull LetexprContext ctx) {
		String alias = ctx.getChild(1).toString();
		if(!alias.contains("?")||alias.contains(" ")){
			Exception e = new Exception();
			System.out.println("Alleged alias: "+ alias);
			e.printStackTrace();
			System.exit(1);
		}
		if(letMap.containsKey(alias)){
			Exception e = new Exception();
			System.out.println("Duplicate alias defn: "+ alias);
			e.printStackTrace();
			System.exit(1);
		}
		if(alias.length()>4){
			Exception e = new Exception();
			System.out.println("Suspicously sized alias: "+ alias);
			e.printStackTrace();
			System.exit(1);
		}
		Expression e = s.pop();

		letMap.put(alias, new Alias(alias, e));
		//letMap.put(alias, e);
	}

	@Override
	public void enterBvnumber(@NotNull BvnumberContext ctx) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void exitBvnumber(@NotNull BvnumberContext ctx) {
		String value = (String)ctx.getChild(1).toString();
		String numBits = (String) ctx.getChild(2).toString();
		
		if(!( numBits.equals("1") || numBits.equals("8") || numBits.equals("16") || numBits.equals("32") || numBits.equals("64"))){
			Exception e = new Exception();
			System.out.println("Improperly sized bits "+ numBits);
			e.printStackTrace();
			//System.exit(1);
		}
		try{
			s.push(new BitVectorConstant(new BigInteger(value), Integer.parseInt(numBits)));
		}catch(Exception e){
			System.out.println("Problem creating constant: "+ value +" " + numBits);
			e.printStackTrace();
			//System.exit(1);
		}
	}

	@Override
	public void enterAssertions(@NotNull AssertionsContext ctx) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void exitAssertions(@NotNull AssertionsContext ctx) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void enterArraySize(@NotNull ArraySizeContext ctx) {
		String value = ctx.getChild(1).toString();
		s.push(new IntConstant(Integer.valueOf(value)));
	}

	@Override
	public void exitArraySize(@NotNull ArraySizeContext ctx) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void enterNothing(@NotNull NothingContext ctx) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void exitNothing(@NotNull NothingContext ctx) {
		if(ctx.getChildCount()>1){
			Expression e = s.pop();
			Operation o = (Operation)s.pop();
			if(o.getOperator().getArity()==2){
				s.push(new Operation(o.getOperator(), o.getOperand(0), e));
			}else if(o.getOperator().getArity()==3){
				s.push(new Operation(o.getOperator(), o.getOperand(0), o.getOperand(1), e));
			}else{
				Exception e1 = new Exception();
				System.out.println("Unhandled nothing operation: "+ o.getOperator().toString());
				e1.printStackTrace();
				System.exit(1);
			}
		}

	}

	@Override
	public void enterBool(@NotNull BoolContext ctx) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void exitBool(@NotNull BoolContext ctx) {
		String bool = ctx.getChild(0).toString();
		if(bool.equals("true")){
			s.push(Operation.BV_TRUE);
		}else if(bool.equals("false")){
			s.push(Operation.BV_FALSE);
		}else{
			Exception e = new Exception();
			System.out.println("Alleged boolean value: "+ bool);
			e.printStackTrace();
			System.exit(1);
		}
	}

	@Override
	public void enterDeclarations(@NotNull DeclarationsContext ctx) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void exitDeclarations(@NotNull DeclarationsContext ctx) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void enterBitManipulation(@NotNull BitManipulationContext ctx) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void exitBitManipulation(@NotNull BitManipulationContext ctx) {
		String op = ctx.getChild(0).toString();
		try{
			op = op.substring(3).trim();
			IntConstant bits = new IntConstant(Integer.parseInt(ctx.getChild(1).toString()));
			if(op.equals("zero_extend")){
				s.push(new Operation(Operation.Operator.BVZEROEXTEND, bits, null));
			}else if(op.equals("sign_extend")){
				s.push(new Operation(Operation.Operator.BVSIGNEXTEND, bits, null));
			}else if(op.equals("extract")){
				IntConstant loc = new IntConstant(Integer.parseInt(ctx.getChild(2).toString()));
				s.push(new Operation(Operation.Operator.BVEXTRACT, bits, loc, null));
			}else{
				Exception e1 = new Exception();
				System.out.println("Alleged operation: "+ op);
				e1.printStackTrace();
				System.exit(1);
			}
		}catch(Exception e1){
			System.out.println("Alleged operation: "+ op);
			e1.printStackTrace();
			System.exit(1);
		}
		
	}
}