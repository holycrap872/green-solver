package za.ac.sun.cs.green.klee;

import static org.junit.Assert.*;

import java.io.FileInputStream;
import java.util.Properties;
import java.util.Set;

import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.parser.klee.KleeOutputParser;
import za.ac.sun.cs.green.parser.klee.TestFrontEnd;
import za.ac.sun.cs.green.service.bvfactorizer.BVFactorExpression;
import za.ac.sun.cs.green.util.Configuration;

public class SmallFactorTest {

	private static Green solver;
	private static Properties props;
	
	@BeforeClass
	public static void buildUp(){
		props = new Properties();
		try {
			props.load(new FileInputStream("helperfiles/klee.properties"));
		} catch (Exception e) {
			System.err.println("Problem loading .properties file");
			System.exit(1);
		}
		solver = new Green(props);
		new Configuration(solver, props).configure();
	}

	@Test
	public void test00() {

		StringBuilder unparsed = new StringBuilder();
		unparsed.append("(set-logic QF_AUFBV )");
		unparsed.append("(declare-fun const_arr1 () (Array (_ BitVec 32) (_ BitVec 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv0 32) ) (_ bv2 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv2 32) ) (_ bv178 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (_ bv0 32) ) ) (_ bv178 32) ) )");
		
		unparsed.append("(check-sat)");
		unparsed.append("(exit)");

		Expression expression = KleeOutputParser.createExpressionKlee(unparsed.toString());


		BVFactorExpression bvf = new BVFactorExpression(solver, null, expression, props);

		Set<Expression> set = bvf.getFactors();
		
		for(Expression e : set){
			System.out.println(e);
		}
		
		assertEquals(set.size(), 1);
	}
	
	@Test
	public void test01() {

		StringBuilder unparsed = new StringBuilder();
		unparsed.append("(set-logic QF_AUFBV )");
		unparsed.append("(declare-fun const_arr1 () (Array (_ BitVec 32) (_ BitVec 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv0 32) ) (_ bv2 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv2 32) ) (_ bv3 32) ) )");
		//unparsed.add("(assert (=  (select const_arr1 (_ bv3 32) ) (_ bv178 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (_ bv2 32) ) ) (_ bv178 32) ) )");

		unparsed.append("(check-sat)");
		unparsed.append("(exit)");

		Expression expression = KleeOutputParser.createExpressionKlee(unparsed.toString());


		BVFactorExpression bvf = new BVFactorExpression(solver, null, expression, props);

		Set<Expression> set = bvf.getFactors();
		
		for(Expression e : set){
			System.out.println(e);
		}
		
		assertEquals(set.size(), 2);
	}
	
	@Test
	public void test02() {

		StringBuilder unparsed = new StringBuilder();
		unparsed.append("(set-logic QF_AUFBV )");
		unparsed.append("(declare-fun const_arr1 () (Array (_ BitVec 32) (_ BitVec 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv0 32) ) (_ bv2 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv2 32) ) (_ bv3 32) ) )");
		//unparsed.add("(assert (=  (select const_arr1 (_ bv3 32) ) (_ bv178 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (select const_arr1 (_ bv0 32) ) ) ) (_ bv178 32) ) )");

		unparsed.append("(check-sat)");
		unparsed.append("(exit)");

		Expression expression = KleeOutputParser.createExpressionKlee(unparsed.toString());


		BVFactorExpression bvf = new BVFactorExpression(solver, null, expression, props);

		Set<Expression> set = bvf.getFactors();
		
		for(Expression e : set){
			System.out.println(e);
		}
		
		assertEquals(set.size(), 1);
	}
	
	@Test
	public void test03() {
		String [] args = {"helperfiles/klee.properties", "helperfiles/partab"};
		TestFrontEnd.main(args);
	}
	
	@AfterClass
	public static void tearDown(){
		solver.report();
	}
}
