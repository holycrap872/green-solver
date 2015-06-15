package za.ac.sun.cs.green.service.z3;

import java.util.HashMap;
import java.util.Stack;

import za.ac.sun.cs.green.expr.Alias;
import za.ac.sun.cs.green.expr.ArrayVariable;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.RealConstant;
import za.ac.sun.cs.green.expr.RealVariable;
import za.ac.sun.cs.green.expr.BitVectorConstant;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.ArrayExpr;
import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BitVecNum;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

public class SubsumptionHelper {

	private HashMap<String, String> cfgModel;
	private Context mainCtx;
	private Solver mainSolver;
	
	private static int sat = 0;
	private static int unsat = 0;
	
	public SubsumptionHelper(){
		cfgModel = new HashMap<String, String>();
		cfgModel.put("model", "true");

		try{
			mainCtx = new Context(cfgModel);
			mainSolver = mainCtx.mkSolver();
		}catch(Z3Exception e){
			e.printStackTrace();
			System.exit(1);
		}
	}
	
	public Boolean solve(Expression e) {		
		try{
			BoolExpr expr = exploreExpression(e, mainCtx);

			Model model = (Model) check(mainCtx, expr, Status.SATISFIABLE, mainSolver);

			boolean ret;
			expr.dispose();
			if(model != null){
				model.dispose();
				sat ++;
				ret = true;
			}else{
				unsat ++;
				ret = false;
			}
			return ret;

		}catch(Z3Exception exception){
			exception.printStackTrace();
			System.exit(1);
			return null;
		}
	}

	private BoolExpr exploreExpression(Expression e, Context ctx) throws Z3Exception{
		Explorer ex = new Explorer(ctx);
		return ex.explore(e);
	}

	private Model check(Context ctx, BoolExpr f, Status sat, Solver s){
		try{
			s.push();
			s.add(f);

			if (s.check() != sat){
				s.pop();

				return null;
			}else if (sat == Status.SATISFIABLE){
				Model ret = s.getModel();
				s.pop();

				return ret;
			}else{
				new java.lang.Exception().printStackTrace();
				System.exit(1);
				return null;
			}
		}catch(Exception e){
			e.printStackTrace();
			System.out.println("Hey dummy");
			System.exit(1);
			return null;
		}
	}
	
	private class Explorer extends Visitor{

		private Context ctx;
		private Stack<Expr> stack;

		public Explorer(Context ctx){
			this.ctx = ctx; 
			this.stack = new Stack<Expr>();
		}

		public BoolExpr explore(Expression expression) {
			try {
				expression.accept(this);
			} catch (VisitorException e) {
				e.printStackTrace();
			}
			return (BoolExpr) stack.pop();
		}

		@Override
		public void postVisit(Variable variable) {
			try{
				if(variable instanceof RealVariable){
					stack.push(ctx.mkRealConst(variable.toString()));
				}else if(variable instanceof IntVariable){
					stack.push(ctx.mkBVConst(variable.toString(), 32));
					//					stack.push(ctx.mkIntConst(variable.toString()));
				}else if(variable instanceof ArrayVariable){
					Sort index = ctx.mkBitVecSort(((ArrayVariable) variable).getIndexSize().getValue());
					Sort mem = ctx.mkBitVecSort(((ArrayVariable) variable).getMemSizeBits().getValue());
					stack.push(ctx.mkArrayConst(variable.getName(), index, mem));
				}else{
					new java.lang.Exception().printStackTrace();
					System.exit(1);
				}
			}catch(Z3Exception e){
				e.printStackTrace();
				System.exit(1);
			}
		}

		@Override
		public void postVisit(Constant constant){
			try{
				if(constant instanceof RealConstant){
					stack.push(ctx.mkReal(constant.toString()));
				}else if(constant instanceof IntConstant){
					stack.push(ctx.mkBV(constant.toString(), 32));
					//					stack.push(ctx.mkInt(constant.toString()));
				}else if(constant instanceof BitVectorConstant){
					stack.push(ctx.mkBV(((BitVectorConstant) constant).getValue().longValue(), ((BitVectorConstant) constant).getNumBits()));
				}else{
					new java.lang.Exception().printStackTrace();
					System.exit(1);
				}
			}catch(Z3Exception e){
				e.printStackTrace();
				System.exit(1);
			}
		}
		
		@Override
		public void postVisit(Alias alias){
			try {
				alias.getExpression().accept(this);
			} catch (VisitorException e) {
				e.printStackTrace();
			}
		}

		@Override
		public void postVisit(Operation operation){
			try{
				if(operation.getOperator() == Operation.Operator.EQ){
					Expr right = stack.pop();
					
					Expr left = null;
					if(stack.size() == 0){
						System.out.println("here");
					}else{
						left = stack.pop();
					}
					if(left instanceof BitVecExpr || right instanceof BitVecExpr){
						if(! (left instanceof BitVecExpr)){
							left = ctx.mkInt2BV(32, (IntExpr)left);
						}
						if(! (right instanceof BitVecExpr)){
							right = ctx.mkInt2BV(32, (IntExpr)right);
						}
					}

					stack.push(ctx.mkEq(left,  right));
				}else if(operation.getOperator() == Operation.Operator.NE){
					Expr right = stack.pop();
					Expr left = stack.pop();
					if(left instanceof BitVecExpr || right instanceof BitVecExpr){
						if(! (left instanceof BitVecExpr)){
							left = ctx.mkInt2BV(32, (IntExpr)left);
						}
						if(! (right instanceof BitVecExpr)){
							right = ctx.mkInt2BV(32, (IntExpr)right);
						}
					}

					stack.push(ctx.mkNot(ctx.mkEq(left,  right)));
				}else if(operation.getOperator() == Operation.Operator.LE){
					Expr right = stack.pop();
					Expr left = stack.pop();
					if(left instanceof BitVecExpr || right instanceof BitVecExpr){
						if(! (left instanceof BitVecExpr)){
							left = ctx.mkInt2BV(32, (IntExpr)left);
						}
						if(! (right instanceof BitVecExpr)){
							right = ctx.mkInt2BV(32, (IntExpr)right);
						}
						stack.push(ctx.mkBVSLE((BitVecExpr) left, (BitVecExpr) right));
					}else{
						stack.push(ctx.mkLe((ArithExpr)left,  (ArithExpr) right));
					}
				}else if(operation.getOperator() == Operation.Operator.LT){
					Expr right = stack.pop();
					Expr left = stack.pop();
					if(left instanceof BitVecExpr || right instanceof BitVecExpr){
						if(! (left instanceof BitVecExpr)){
							left = ctx.mkInt2BV(32, (IntExpr)left);
						}
						if(! (right instanceof BitVecExpr)){
							right = ctx.mkInt2BV(32, (IntExpr)right);
						}
						stack.push(ctx.mkBVSLT((BitVecExpr) left, (BitVecExpr) right));
					}else{
						stack.push(ctx.mkLt((ArithExpr)left,  (ArithExpr) right));
					}
				}else if(operation.getOperator() == Operation.Operator.GE){
					Expr right = stack.pop();
					Expr left = stack.pop();
					if(left instanceof BitVecExpr || right instanceof BitVecExpr){
						if(! (left instanceof BitVecExpr)){
							left = ctx.mkInt2BV(32, (IntExpr)left);
						}
						if(! (right instanceof BitVecExpr)){
							right = ctx.mkInt2BV(32, (IntExpr)right);
						}
						stack.push(ctx.mkBVSGE((BitVecExpr) left, (BitVecExpr) right));
					}else{
						stack.push(ctx.mkGe((ArithExpr)left,  (ArithExpr) right));
					}
				}else if(operation.getOperator() == Operation.Operator.GT){
					Expr right = stack.pop();
					Expr left = stack.pop();
					if(left instanceof BitVecExpr || right instanceof BitVecExpr){
						if(! (left instanceof BitVecExpr)){
							left = ctx.mkInt2BV(32, (IntExpr)left);
						}
						if(! (right instanceof BitVecExpr)){
							right = ctx.mkInt2BV(32, (IntExpr)right);
						}
						stack.push(ctx.mkBVSGT((BitVecExpr) left, (BitVecExpr) right));
					}else{
						stack.push(ctx.mkGt((ArithExpr)left,  (ArithExpr) right));
					}
				}else if(operation.getOperator() == Operation.Operator.AND){
					BoolExpr right = (BoolExpr) stack.pop();
					BoolExpr left = (BoolExpr) stack.pop();
					stack.push(ctx.mkAnd(left,  right));
				}else if(operation.getOperator() == Operation.Operator.ADD){
					Expr right = stack.pop();
					Expr left = stack.pop();

					if(left instanceof BitVecExpr || right instanceof BitVecExpr){
						if(! (left instanceof BitVecExpr)){
							left = ctx.mkInt2BV(32, (IntExpr)left);
						}
						if(! (right instanceof BitVecExpr)){
							right = ctx.mkInt2BV(32, (IntExpr)right);
						}
						stack.push(ctx.mkBVAdd((BitVecExpr)left,  (BitVecExpr)right));
					}else{
						stack.push(ctx.mkAdd((ArithExpr)left,  (ArithExpr)right));
					}
				}else if(operation.getOperator() == Operation.Operator.SUB){
					Expr right = stack.pop();
					Expr left = stack.pop();

					if(left instanceof BitVecExpr || right instanceof BitVecExpr){
						if(! (left instanceof BitVecExpr)){
							left = ctx.mkInt2BV(32, (IntExpr)left);
						}
						if(! (right instanceof BitVecExpr)){
							right = ctx.mkInt2BV(32, (IntExpr)right);
						}
						stack.push(ctx.mkBVSub((BitVecExpr)left,  (BitVecExpr)right));
					}else{
						stack.push(ctx.mkSub((ArithExpr)left,  (ArithExpr)right));
					}
				}else if(operation.getOperator() == Operation.Operator.MUL){
					Expr right = stack.pop();
					Expr left = stack.pop();

					if(left instanceof BitVecExpr || right instanceof BitVecExpr){
						if(! (left instanceof BitVecExpr)){
							left = ctx.mkInt2BV(32, (IntExpr)left);
						}
						if(! (right instanceof BitVecExpr)){
							right = ctx.mkInt2BV(32, (IntExpr)right);
						}
						stack.push(ctx.mkBVMul((BitVecExpr)left,  (BitVecExpr)right));
					}else{
						stack.push(ctx.mkMul((ArithExpr)left,  (ArithExpr)right));
					}
				}else if(operation.getOperator() == Operation.Operator.OR){
					BoolExpr right = (BoolExpr) stack.pop();
					BoolExpr left = (BoolExpr) stack.pop();
					stack.push(ctx.mkOr(left,  right));
				}else if(operation.getOperator() == Operation.Operator.DIV){
					Expr right = stack.pop();
					Expr left = stack.pop();

					if(left instanceof BitVecExpr || right instanceof BitVecExpr){
						if(! (left instanceof BitVecExpr)){
							left = ctx.mkInt2BV(32, (IntExpr)left);
						}
						if(! (right instanceof BitVecExpr)){
							right = ctx.mkInt2BV(32, (IntExpr)right);
						}
						stack.push(ctx.mkBVSDiv((BitVecExpr)left,  (BitVecExpr)right));
					}else{
						stack.push(ctx.mkDiv((ArithExpr)left,  (ArithExpr)right));
					}
				}else if(operation.getOperator() == Operation.Operator.SQRT){
					ArithExpr right = (ArithExpr) stack.pop();
					stack.push(ctx.mkSub(right, ctx.mkReal("0.5")));
				}else if(operation.getOperator() == Operation.Operator.BVAND){
					Expr right = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					if(right instanceof ArithExpr){
						right = ctx.mkInt2BV(32, (IntExpr) right);
					}

					if(left instanceof ArithExpr){
						left = ctx.mkInt2BV(32, (IntExpr) left);
					}
					stack.push(ctx.mkBVAND((BitVecExpr)left, (BitVecExpr) right));

				}else if(operation.getOperator() == Operation.Operator.BVOR){
					Expr right = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					if(right instanceof ArithExpr){
						right = ctx.mkInt2BV(32, (IntExpr) right);
					}

					if(left instanceof ArithExpr){
						left = ctx.mkInt2BV(32, (IntExpr) left);
					}
					stack.push(ctx.mkBVOR((BitVecExpr)left, (BitVecExpr) right));

				}else if(operation.getOperator() == Operation.Operator.BVXOR){
					Expr right = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					if(right instanceof ArithExpr){
						right = ctx.mkInt2BV(32, (IntExpr) right);
					}

					if(left instanceof ArithExpr){
						left = ctx.mkInt2BV(32, (IntExpr) left);
					}
					stack.push(ctx.mkBVXOR((BitVecExpr)left, (BitVecExpr) right));

				}
				else if(operation.getOperator() == Operation.Operator.BVLSHL){
					Expr right = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					if(right instanceof ArithExpr){
						right = ctx.mkInt2BV(32, (IntExpr) right);
					}

					if(left instanceof ArithExpr){
						left = ctx.mkInt2BV(32, (IntExpr) left);
					}
					stack.push(ctx.mkBVSHL((BitVecExpr)left, (BitVecExpr) right));

				}else if(operation.getOperator() == Operation.Operator.BVASHR){
					Expr right = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					if(right instanceof ArithExpr){
						right = ctx.mkInt2BV(32, (IntExpr) right);
					}

					if(left instanceof ArithExpr){
						left = ctx.mkInt2BV(32, (IntExpr) left);
					}
					stack.push(ctx.mkBVASHR((BitVecExpr)left, (BitVecExpr) right));

				}else if(operation.getOperator() == Operation.Operator.BVLSHR){
					Expr right = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					if(right instanceof ArithExpr){
						right = ctx.mkInt2BV(32, (IntExpr) right);
					}

					if(left instanceof ArithExpr){
						left = ctx.mkInt2BV(32, (IntExpr) left);
					}
					stack.push(ctx.mkBVLSHR((BitVecExpr)left, (BitVecExpr) right));

				}else if(operation.getOperator() == Operation.Operator.MOD){
					Expr right = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					if(right instanceof ArithExpr){
						right = ctx.mkInt2BV(32, (IntExpr) right);
					}

					if(left instanceof ArithExpr){
						left = ctx.mkInt2BV(32, (IntExpr) left);
					}
					stack.push(ctx.mkBVSMod((BitVecExpr)left, (BitVecExpr) right));

				}else if(operation.getOperator() == Operation.Operator.SELECT){
					Expr right = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					stack.push(ctx.mkSelect((ArrayExpr) left, right));
				}else if(operation.getOperator() == Operation.Operator.STORE){
					Expr right = (Expr) stack.pop();
					Expr middle = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					stack.push(ctx.mkStore((ArrayExpr) left, middle, right));
				}else if(operation.getOperator() == Operation.Operator.CONCAT){
					Expr right = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					stack.push(ctx.mkConcat((BitVecExpr)left, (BitVecExpr)right));
				}else if(operation.getOperator() == Operation.Operator.BVSGE){
					Expr right = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					stack.push(ctx.mkBVSGE((BitVecExpr)left, (BitVecExpr)right));
				}else if(operation.getOperator() == Operation.Operator.BVSGT){
					Expr right = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					stack.push(ctx.mkBVSGT((BitVecExpr)left, (BitVecExpr)right));
				}else if(operation.getOperator() == Operation.Operator.BVSLE){
					Expr right = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					stack.push(ctx.mkBVSLE((BitVecExpr)left, (BitVecExpr)right));
				}else if(operation.getOperator() == Operation.Operator.BVSLT){
					Expr right = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					stack.push(ctx.mkBVSLT((BitVecExpr)left, (BitVecExpr)right));
				}else if(operation.getOperator() == Operation.Operator.ITE){
					Expr right = (Expr) stack.pop();
					Expr middle = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					stack.push(ctx.mkITE((BoolExpr)left, middle, right));
				}else if(operation.getOperator() == Operation.Operator.BVUGE){
					Expr right = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					stack.push(ctx.mkBVUGE((BitVecExpr)left, (BitVecExpr)right));
				}else if(operation.getOperator() == Operation.Operator.BVUGT){
					Expr right = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					stack.push(ctx.mkBVUGT((BitVecExpr)left, (BitVecExpr)right));
				}else if(operation.getOperator() == Operation.Operator.BVULE){
					Expr right = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					stack.push(ctx.mkBVULE((BitVecExpr)left, (BitVecExpr)right));
				}else if(operation.getOperator() == Operation.Operator.BVULT){
					Expr right = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					stack.push(ctx.mkBVULT((BitVecExpr)left, (BitVecExpr)right));
				}else if(operation.getOperator() == Operation.Operator.BVSUB){
					Expr right = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					stack.push(ctx.mkBVSub((BitVecExpr)left, (BitVecExpr)right));
				}else if(operation.getOperator() == Operation.Operator.BVSIGNEXTEND){
					Expr right = (Expr) stack.pop();
					int left = ((BitVecNum) stack.pop()).getInt();
					stack.push(ctx.mkSignExt(left, (BitVecExpr)right));
				}else if((operation.getOperator() == Operation.Operator.BVSHL) || (operation.getOperator() == Operation.Operator.BVLSHL)){
					Expr right = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					stack.push(ctx.mkBVSHL((BitVecExpr) left, (BitVecExpr)right));
				}else if(operation.getOperator() == Operation.Operator.BVASHR){
					Expr right = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					stack.push(ctx.mkBVASHR((BitVecExpr) left, (BitVecExpr)right));
				}else if(operation.getOperator() == Operation.Operator.BVLSHR){
					Expr right = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					stack.push(ctx.mkBVLSHR((BitVecExpr) left, (BitVecExpr)right));
				}else if(operation.getOperator() == Operation.Operator.BVMUL){
					Expr right = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					stack.push(ctx.mkBVMul((BitVecExpr) left, (BitVecExpr)right));
				}else if(operation.getOperator() == Operation.Operator.BVEXTRACT){
					Expr right = (Expr) stack.pop();
					int middle = ((BitVecNum) stack.pop()).getInt();
					int left = ((BitVecNum)(Expr) stack.pop()).getInt();
					stack.push(ctx.mkExtract(left, middle, (BitVecExpr)right));
				}else if(operation.getOperator() == Operation.Operator.BVADD){
					Expr right = (Expr) stack.pop();
					Expr left = (Expr) stack.pop();
					stack.push(ctx.mkBVAdd((BitVecExpr) left, (BitVecExpr)right));
				}else{
					System.out.println(operation.getOperator().toString());
					new java.lang.Exception().printStackTrace();
					System.exit(1);
				}
			}catch(Z3Exception e){
				e.printStackTrace();
				System.exit(1);
			}
		}	
	}
}
