package rddl;

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.HashMap;

import rddl.RDDL.LCONST;
import rddl.RDDL.PVAR_NAME;

public class Expression {
	
	public Expression(){
		_exp = new ArrayList<Expression.PolyNomial>();
		_const = 0;
	}
	
	//construct object with the const
	public Expression(double theCons){
		_exp = new ArrayList<Expression.PolyNomial>();
		_const = theCons;
	}
	
	//copy another expression
	public Expression(Expression theExp){
		_exp = new ArrayList<Expression.PolyNomial>();
		for(PolyNomial thePN: theExp._exp){
			_exp.add(new PolyNomial(thePN));
		}
		_const = theExp._const;
	}
	
	//construct object with only one nomial
	public Expression(String theVarName, int power) {
		Nomial n = new Nomial(theVarName, power);
		PolyNomial pn = new PolyNomial();
		pn.item.add(n);
		_exp = new ArrayList<Expression.PolyNomial>();
		_exp.add(pn);
		_const = 0;
	}
	
	//say x^2
	class Nomial{
		String varName;
		int power;
		public Nomial(){
			varName = null;
			power = 0;
		}
		public Nomial(String theVarName, int thePower) {
			// TODO Auto-generated constructor stub
			varName = theVarName;
			power = thePower;
		}
	}
	
	//say -3xy^2
	class PolyNomial{
		public PolyNomial(){
			preConst = 1;
			item = new ArrayList<Expression.Nomial>();
		}
		public PolyNomial(PolyNomial thePN){
			preConst = thePN.preConst;
			item = new ArrayList<Expression.Nomial>();
			for(Nomial n: thePN.item){
				item.add(new Nomial(n.varName, n.power));
			}
		}
		ArrayList<Nomial> item;
		double preConst;
		boolean IfSamePNomial(PolyNomial pn){
			if(item.size() != pn.item.size()){
				return false;
			}
			for(Nomial n: item){
				boolean ifExist = false;
				for(Nomial cn: pn.item){
					if(n.varName.equals(cn.varName) && n.power == cn.power){
						ifExist = true;
						break;
					}
				}
				if(!ifExist){
					return false;
				}
			}
			return true;
		}
	}
	
	//say -3xy^2 + y^3z -2x^2y
	public ArrayList<PolyNomial> _exp;
	
	public double _const;
	
	//create a new PNomial, copy the content of thePNomial
	//add new PNomial to the expression
	//with const to multiply
	private void AddNewPNomial(PolyNomial thePNomial, double theCon){
		PolyNomial newPNomial = new PolyNomial();
		for(Nomial rightNomial: thePNomial.item){
			newPNomial.item.add(new Nomial(rightNomial.varName, rightNomial.power));
		}
		newPNomial.preConst = theCon;
		if(newPNomial.preConst != 0){
			_exp.add(newPNomial);
		}
	}
	
	//check if newPNomial already exsits in ori expression
	//if yes just add preconst; otherwise add newPNomial to this expression
	private void AddNewPNomialWithCheck(PolyNomial newPNomial, double theCons){
		// wanna check if this already exists in the expression
		boolean ifAlradyExsit = false;
		for (PolyNomial eachPNomial : _exp) {
			if (newPNomial.IfSamePNomial(eachPNomial)) {
				eachPNomial.preConst += theCons; 
				if(eachPNomial.preConst == 0){
					_exp.remove(eachPNomial);
				}
				ifAlradyExsit = true;
				break;
			}
		}
		if(!ifAlradyExsit){
			AddNewPNomial(newPNomial, theCons);
		}
	}
	
	
	//plus another expression
	//minus if the last parameter is set to be "false"
	public Expression Plus(Expression leftExp, Expression rightExp, boolean realPlus){
		Expression newExpression = new Expression();
		//load left expression to new expression
		for(PolyNomial leftPNomial: leftExp._exp){
			newExpression.AddNewPNomial(leftPNomial, leftPNomial.preConst);
		}
		

		//try adding right expression to new expression
		for(PolyNomial rightPNomial: rightExp._exp){
			//if not real plus, meaning minus, first turn all const of right expression to negative
			if(!realPlus){
				PolyNomial newPn = new PolyNomial(rightPNomial);
				newPn.preConst = -rightPNomial.preConst;
				newExpression.AddNewPNomialWithCheck(newPn, newPn.preConst);
			}
			else{
				newExpression.AddNewPNomialWithCheck(rightPNomial, rightPNomial.preConst);
			}
		}
		//const is just sum of const of the two expressions
		if(!realPlus){
			newExpression._const = leftExp._const - rightExp._const;
		}
		else{
			newExpression._const = leftExp._const + rightExp._const;
		}
		return newExpression;
	}
	
	//times another expression
	public Expression Multiply(Expression leftExp, Expression rightExp){
		Expression newExpression = new Expression();
		
		//calculate the product of polynomials
		for(PolyNomial leftNomial: leftExp._exp){
			for(PolyNomial rightNomial: rightExp._exp){
				PolyNomial newNomial = new PolyNomial();
				newNomial.preConst = leftNomial.preConst * rightNomial.preConst;
				//first just copy each normial of the left into new polynomial
				for(Nomial left: leftNomial.item){
					newNomial.item.add(new Nomial(left.varName, left.power));
				}
				//try to add each right nomial into new Polynomial
				for(Nomial right: rightNomial.item){
					//check if each right nomial already exist in left polynomial
					boolean ifSameVarName = false;
					for(Nomial i: newNomial.item){
						if(i.varName.equals(right.varName)){
							i.power += right.power;
							ifSameVarName = true;
							break;
						}
					}
					//if not exist, simply add right nomial into left polynomial
					if(!ifSameVarName){
						newNomial.item.add(new Nomial(right.varName, right.power));
					}
				}
				//now the new polynomial is all set
				//wanna check if this already exists in the expression
				boolean ifAlradyExsit = false;
				for(PolyNomial eachPNomial: newExpression._exp){
					if(newNomial.IfSamePNomial(eachPNomial)){
						eachPNomial.preConst += newNomial.preConst;
						ifAlradyExsit = true;
						break;
					}
				}
				if(!ifAlradyExsit){
					newExpression._exp.add(newNomial);
				}
			}
		}
		for(PolyNomial leftPNomial: leftExp._exp){
			newExpression.AddNewPNomialWithCheck(leftPNomial, leftPNomial.preConst * rightExp._const);
		}
		for(PolyNomial rightPNomial: rightExp._exp){
			newExpression.AddNewPNomialWithCheck(rightPNomial, rightPNomial.preConst * leftExp._const);
		}
		newExpression._const = leftExp._const * rightExp._const;
		return newExpression;
	}
	
	//div another expression
	//only support expression without polynomials for now
	public Expression Div(Expression leftExp, Expression rightExp) throws EvalException{
		if(rightExp._exp.size() != 0){
			throw new EvalException("divier mush be constant!");
		}
		Expression newExp = new Expression();
		for(int i = 0; i < leftExp._exp.size(); i ++){
			newExp.AddNewPNomial(leftExp._exp.get(i), leftExp._exp.get(i).preConst / rightExp._const);
		}
		newExp._const = leftExp._const / rightExp._const;
		return newExp;
	}
	
	//get the real value of a expression
	public double RealValue(PolyNomial pn, HashMap<String, Double> values){
		double pnValue = 1;
		for(Nomial n: pn.item){
			double result = 1;
			for(int i = 1; i <= n.power; i ++){
				if(!values.containsKey(n.varName)){
					@SuppressWarnings("unused")
					int a = 1;
				}
				result *= values.get(n.varName);
			}
			pnValue *= result;
		}
		pnValue *= pn.preConst;
		return pnValue;
	}

	//get the real value of a expression
	public double RealValue(HashMap<String, Double> values){
		double realv = 0;
		//Deal with each poly nomial
		for(PolyNomial pn: _exp){
			realv += RealValue(pn, values);
		}
		realv += _const;
		return realv;
	}
	
	public void Shorten(HashMap<String,Double> currentValue, double maxLength){
		//a new arraylist to store reserved polynomials
		ArrayList<PolyNomial> newPNS = new ArrayList<Expression.PolyNomial>();
		//traverse each pnomial
		// cut by preconst < threshold
		if(maxLength < 1){
			//traverse each pnomial
			for(int i = 0; i < _exp.size(); i ++){
				PolyNomial pn = _exp.get(i);
				if(Math.abs(pn.preConst) < maxLength){
					_const += RealValue(_exp.get(i), currentValue);
					_exp.remove(i);
					i--;
				}
			}
		}
		else{	
			for (int i = 0; i < _exp.size(); i++) {
				PolyNomial pn = _exp.get(i);
				double pnVal = RealValue(pn, currentValue);
				boolean ifInserted = false;
				int index = 0;
				for (PolyNomial comparePN : newPNS) {
					if (Math.abs(RealValue(comparePN, currentValue)) < Math
							.abs(RealValue(pn, currentValue))) {
						newPNS.add(index, pn);
						ifInserted = true;
						if (newPNS.size() > maxLength) {
							_const += RealValue(newPNS.get(newPNS.size() - 1),
									currentValue);
							newPNS.remove(newPNS.size() - 1);

						}
						break;
					}
					index++;
				}
				if (!ifInserted && newPNS.size() < maxLength) {
					newPNS.add(newPNS.size(), pn);
				}
			}
			_exp = newPNS;
		}
	}

	public String toString(){
		String str = new String();
		for(int i = 0; i < _exp.size(); i ++){
			if(i != 0 && _exp.get(i).preConst > 0){
				str += ("+");
			}
			if(_exp.get(i).preConst != 1){
				str += _exp.get(i).preConst;
			}
			ArrayList<Nomial> n = _exp.get(i).item;
			for(int j = 0; j < n.size(); j ++){
				str += n.get(j).varName;
				if(n.get(j).power != 1){
					str += "^(";
					str += n.get(j).power;
					str += ")";
				}
			}
		}
		if(_exp.size() > 0 && _const > 0){
			str += "+";
		}
		str += _const;
		return str;
	}
	
	//get gratdient expression 
	//only supports that we only have one variable
	public Expression Gradient(){
		Expression gradient = new Expression();
		for(PolyNomial thePN: _exp){
			PolyNomial newPn = new PolyNomial();
			int thePower = thePN.item.get(0).power;
			newPn.preConst = thePN.preConst * thePower;
			if(newPn.preConst == 0){
				continue;
			}
			if(thePower == 1){
				gradient._const += newPn.preConst;
				continue;
			}
			newPn.item.add(new Nomial(thePN.item.get(0).varName, thePower - 1));
			gradient._exp.add(newPn);
		}
		return gradient;
	}
	
	//get gradient function w r t a specific variable
	public Expression Gradient(String graNomial){
		Expression gradient = new Expression();
		for(PolyNomial thePN: _exp){
			boolean ifKeep = false;
			PolyNomial newPn = new PolyNomial();
			newPn.preConst = thePN.preConst;
			for(Nomial theN: thePN.item){
				if(theN.varName.equals(graNomial)){
					int newPower = theN.power - 1;
					if(newPower != 0){
						newPn.item.add(new Nomial(theN.varName, newPower));
					}
					newPn.preConst *= theN.power;
					ifKeep = true;
				}
				else{
					newPn.item.add(new Nomial(theN.varName, theN.power));
				}
			}
			if(ifKeep){
				gradient._exp.add(newPn);
			}
		}
		return gradient;
	}
}
