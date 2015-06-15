package za.ac.sun.cs.green.parser.klee;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.LinkedList;
import java.util.List;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

import antlr.SMTLexer;
import antlr.SMTParser;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.resources.Pair;
import za.ac.sun.cs.green.resources.Tri;

public class KleeOutputParser{

	private BufferedReader br;
	private List<Pair<Expression, Boolean>> buffer;

	public KleeOutputParser(File file){
		try {
			br = new BufferedReader(new InputStreamReader(new FileInputStream(file)));
		} catch (IOException e) {
			throw new java.lang.RuntimeException();
		}
		this.buffer = new LinkedList<Pair<Expression, Boolean>>();
	}

	public boolean hasNext() {
		if(buffer.size() > 0){
			return true;
		}

		try{
			Pair<Expression, Boolean> exp = createNextExpression();
			if(exp != null){
				buffer.add(exp);
			}
			return buffer.size() > 0;
		}catch(IOException e){
			return false;
		}
	}

	public Pair<Expression, Boolean> getNext() {
		if(buffer.size() > 0){
			return buffer.remove(0);
		}else{
			return null;
		}
	}

	public void close(){
		try {
			br.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	/*
	 * Gets the ENTIRE part of the query, from the initial (set-logic) statement to the (exit) of the constraint
	 */
	private Pair<Expression, Boolean> createNextExpression() throws IOException{
		String query = null;
		Boolean sat = null;
		while(br.ready() && (query == null || sat == null)){
			String holder = br.readLine();
			if(holder.startsWith("(set-logic")){
				StringBuilder q = new StringBuilder(100000);
				while(holder!=null && !holder.startsWith("(check-sat") && (holder.startsWith("(declar")||holder.startsWith("(set") || holder.startsWith("(assert"))){
					q.append(holder.trim());
					if(br.ready()){
						holder = br.readLine();
					}else{
						holder = null;
					}
				}
				if(holder!=null && holder.startsWith("(check-sat")){
					q.append("(check-sat)");
					q.append("(exit)");
					query = q.toString();
				}
			}else{
				if(holder.contains(";   Solvable:")){
					if(holder.contains("false")){
						sat = false;
					}else if(holder.contains("true")){
						sat = true;
					}else{
						throw new java.lang.RuntimeException();
					}
				}
			}
		}

		if(query == null || sat == null){
			return null;
		}else{
			return new Pair<Expression, Boolean>(KleeOutputParser.createExpressionKlee(query), sat);
		}
	}


	/*
	 * Input: A 
	 * 
	 * Goes through each element in the list
	 * 1) Sets up initial array data with a series of "ands" and returns the expression
	 * 2) Builds on that expression by adding crap to it
	 */
	public static Expression createExpressionKlee(String query){
		//Parse the string
		ANTLRInputStream in = new ANTLRInputStream(query);
		SMTLexer lexer = new SMTLexer(in);
		CommonTokenStream tokens = new CommonTokenStream(lexer);
		SMTParser parser = new SMTParser(tokens);

		//Create Expression from tree
		ParseTree tree = parser.root();
		KleeListener al = new KleeListener(tree);
		Expression e = al.getExpression();

		if(e == null){
			System.out.println("Offending constraint");
			System.out.println(query);
			throw new java.lang.RuntimeException();
		}else{
			return e;
		}
	}
}