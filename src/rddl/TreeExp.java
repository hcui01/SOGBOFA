package rddl;

import java.beans.FeatureDescriptor;
import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import rddl.competition.Records;



public class TreeExp {
	
	class Term{
		double coefficient;
		int var;
		public Term(double c){
			coefficient = c;
			// var = 1 means this is a pure number 
			var = -1;
		}
		public Term(double c, int v){
			coefficient = c;
			// var = 1 means this is a pure number 
			var = v;
		}
		public Term(Term t){
			var = t.var;
			coefficient = t.coefficient;
		}
	} 
	//node type has "SUM"/"MIN"/"PRO"/"DIV"/"LEA"/
	
	String expType;
	//if a node is leaf, then there is a term assgined to it
	Term term = null;
	//if a node is not leaf, then it has children
	public ArrayList<TreeExp> subExp = null;
	//pointer to the father
	public ArrayList<TreeExp> father = null;

	public int counter; 
	
	boolean ifInQ = false;
	
	int printCounter = 0;
	
	public TreeExp(){};
	
	//constructor with the type and father
	public TreeExp(String type, TreeExp f){
		if(father == null){
			father = new ArrayList<TreeExp>();
		}
		if(f != null)
		father.add(f);
		expType = new String(type);
		
		term = null;
		subExp = new ArrayList<TreeExp>();
	}
	
	//constructor for a number and father
	public TreeExp(double constant, TreeExp f){
		if(father == null){
			father = new ArrayList<TreeExp>();
		}
		if(f != null)
		father.add(f);
		expType = "LEA";
		term = new Term(constant, -1);
		subExp = null;
	}
	
	//constructor for a variable and father
	public TreeExp(int v, TreeExp f) {
		if(father == null){
			father = new ArrayList<TreeExp>();
		}
		if(f != null)
		father.add(f);
		expType = "LEA";
		term = new Term(1, v);
		subExp = null;
	}
	


	//take gradient of oriExp wrt var
	//fill in the content for gradient exp
	private double GetGradientForTerm(int v){
		if(v == term.var){
			return term.coefficient;
		}
		else{
			return 0;
		}
	}
	
	
	
	
	//Get realvalue of a tree
	public double RealValue(ArrayList<Double> varVal, HashMap<TreeExp, Double> valRec) throws EvalException{

		if(valRec.containsKey(this)){
			return valRec.get(this); 
		}
		else{
			double r = 0;
			if(expType.equals("LEA")){
				if(term.var == -1){
					r = term.coefficient;
				}
				else{
					r = varVal.get(term.var) * term.coefficient;
				}
			}
			else{
				if(expType.equals("SUM")){
					r = 0;

					for(TreeExp subT: subExp){
						double v = subT.RealValue(varVal, valRec);

						r += v;
					}

				}
				else{
					if(expType.equals("MIN")){
						if(subExp.size() == 0){
							@SuppressWarnings("unused")
							int a  = 1;
						}
						r = subExp.get(0).RealValue(varVal, valRec);
						for(int i = 1; i < subExp.size(); i ++){
							r -= subExp.get(i).RealValue(varVal, valRec);	
						}
					}
					else{
						if(expType.equals("PRO")){
							r = 1;
							
							for(TreeExp subT: subExp){
								double v = subT.RealValue(varVal, valRec);
								r *= v;

								if(r == 0){
									break;
								}
							}
						}
						else{
							if(expType.equals("DIV")){
								if(subExp.size() != 2){
									throw new EvalException("DIVISION has to have two childean!");
								}
								
								r = subExp.get(0).RealValue(varVal, valRec) / subExp.get(1).RealValue(varVal, valRec);	
							}
							else{
								throw new EvalException ("realValue: can only have operator SUM/DIV/PRO/MIN");
							}
						}
					}
				}
			}
			
			valRec.put(this, r);
			return r;
		}
	}
	
	
	
	
	//see bellow
	public void ClearFather(){
		father.clear();
		if(subExp != null){
			for(TreeExp child: subExp){
			
			child.ClearFather();
			child.father.add(this);
			}
		}
	}
	//get the gradients for variables using gradient tree
	// used for reverse accumulation
	public double GetPartialGradient(boolean sortGurentee, HashMap<TreeExp, Double> partialDev,
			ArrayList<Double> varVal, HashMap<TreeExp, Double> valRec)
			throws EvalException {
		double thePartDev = 0;
		for (TreeExp f : father) {
			if (f == null || !f.ifInQ) {
				continue;
			}
			// the partial gradient of f to this
			double selfDev = 1;
			// the partial gradient of Q to f

			double fatherPartDev = 0;
			if (partialDev.containsKey(f)) {
				fatherPartDev = partialDev.get(f);

			} else {
				if(sortGurentee){
					throw new EvalException("father hasn't been calculated");
				}else{
					fatherPartDev = f.GetPartialGradient(sortGurentee, partialDev, varVal, valRec);
				}
			}
			if (f.expType.equals("SUM")) {
				selfDev = 1;
			} else {
				if (f.expType.equals("PRO")) {
					for (TreeExp sibling : f.subExp) {
						if (sibling.equals(this)) {
							continue;
						}
						selfDev *= sibling.RealValue(varVal, valRec);
					}
				} else {
					if (f.expType.equals("DIV")) {
						if (f.subExp.get(0) == this) {
							selfDev /= f.subExp.get(1)
									.RealValue(varVal, valRec);
						} else {
							selfDev = -1
									/ Math.pow(
											f.subExp.get(1).RealValue(varVal,
													valRec), 2);
						}
					} else {
						if (f.expType.equals("MIN")) {
							if (f.subExp.get(0) == this) {
								selfDev = 1;
							} else {
								selfDev = -1;
							}
						}
					}
				}
			}
			thePartDev += selfDev * fatherPartDev;
		}
		partialDev.put(this, thePartDev);
		return thePartDev;
	}
	
	
	
	//clear F
	//remove the nodes that are not relatd to F
	public void MarkForQ(){
		this.ifInQ = true;
		if(this.subExp!= null){
			for(TreeExp child: this.subExp){
				if(!child.ifInQ){
					child.MarkForQ();
				}
			}
		}
	}
	public void CountFather(HashMap<TreeExp, Integer> fatherCounter){
		if(father!=null){
			//ArrayList<TreeExp> deletFather = new ArrayList<TreeExp>();
			int fadeFather = 0;
			for(TreeExp f: father){
				if(!f.ifInQ){
					fadeFather ++;
					//f.subExp.remove(this);
				}
			}
			//father.removeAll(deletFather);
			fatherCounter.put(this, father.size() - fadeFather);
		}
		else{
			fatherCounter.put(this, 0);
		}
		if(subExp != null){
			for(TreeExp child: subExp){
				if(!fatherCounter.containsKey(child)){
					child.CountFather(fatherCounter);
				}
			}
		}
	}
	public HashMap<TreeExp, Integer> ClearF(){
		//width first search all nodes starting from 
		//long t00 = System.currentTimeMillis();
		MarkForQ();
		//System.out.println(System.currentTimeMillis() - t00);
		//Search Again to delete fathers that are not in the tree
		//ArrayList<TreeExp> deletFathers = new ArrayList<TreeExp>();
		//t00 = System.currentTimeMillis();
		HashMap<TreeExp, Integer> fatherCounter = new HashMap<TreeExp, Integer>();
		CountFather(fatherCounter);
		//System.out.println(System.currentTimeMillis() - t00);
		return fatherCounter;
	}
	
	public void GenUnsortQue(HashMap<TreeExp, Boolean> ifVisited, ArrayList<TreeExp> res){
		res.add(this);
		ifVisited.put(this, true);
		if(subExp != null){
			for(TreeExp child: subExp){
				if(!ifVisited.containsKey(child)){
					child.GenUnsortQue(ifVisited, res);
				}
			}
		}
	}
	
	//topological sorting
	public ArrayList<TreeExp> TopologQueue(boolean ifSort) {
		ArrayList<TreeExp> queue = new ArrayList<TreeExp>();
		if(ifSort){
			HashMap<TreeExp, Integer> fatherCounter = ClearF();
			//long t00 = System.currentTimeMillis();
			ArrayList<TreeExp> noFather = new ArrayList<TreeExp>();
			//HashMap<TreeExp, Integer> fatherCounter = new HashMap<TreeExp, Integer>();
			noFather.add(this);
			// this could be dangeous
			int noFatherCounter = 0;
			while (noFatherCounter != noFather.size()) {
				// pop out the first item of noFather
				TreeExp currentNoF = noFather.get(noFatherCounter);
				queue.add(currentNoF);
				if (!currentNoF.expType.equals("LEA")) {
					for (TreeExp child : currentNoF.subExp) {
						if(currentNoF == this && !fatherCounter.containsKey(child)){
							continue;
						}
						int fSize = fatherCounter.get(child);

						if (fSize == 1) {
							fatherCounter.put(child, 0);
							noFather.add(child);

						} else {
							if (fSize != 0) {
								fatherCounter.put(child, fSize - 1);
							}
						}
					}
				}
				noFatherCounter++;
			}
			//System.out.println(System.currentTimeMillis() - t00);
			/*
			 * Iterator<?> iter = fatherCounter.entrySet().iterator(); while
			 * (iter.hasNext()) { Map.Entry entry = (Map.Entry) iter.next();
			 * TreeExp key = (TreeExp)entry.getKey();
			 * 
			 * if(key.expType.equals("LEA") && key.term.var!=-1){
			 * queue.add(key); } }
			 */
		}
		else{
			MarkForQ();
			GenUnsortQue(new HashMap<TreeExp, Boolean>(), queue);
		}
		return queue;
	}
	
	private void PrintDev(TreeExp Q, HashMap<TreeExp, Double> dev, HashMap<TreeExp, Boolean> ifPrinted){
		printCounter ++;
		System.out.println(printCounter + " " + dev.get(Q));
		ifPrinted.put(Q, true);
		if(Q.subExp!=null)
		for(TreeExp child: Q.subExp){
			if(!ifPrinted.containsKey(child))
			PrintDev(child, dev, ifPrinted);
		}
	}
	
	//get the gadient tree for F
	//used for reverse accumulation
	public void RevAccGradient(boolean ifSort, ArrayList<TreeExp> que, ArrayList<Double> delta, ArrayList<Double> varVal) throws EvalException{
		HashMap<Integer, Double> result = new HashMap<Integer, Double>();
		HashMap<TreeExp, Double> partialDev = new HashMap<TreeExp, Double>();
		HashMap<TreeExp, Double> valRec = new HashMap<TreeExp, Double>();
		
		int queIndex = 0;
		while(queIndex < que.size()){
			//pop que[index]
			TreeExp currentT = que.get(queIndex);
			double thePartialDev = 0;
			if(currentT == this){
				thePartialDev = 1;
				partialDev.put(this, 1.0);
			}
			else{
				thePartialDev = currentT.GetPartialGradient(ifSort, partialDev, varVal,valRec);
			}
			
			if (currentT.expType.equals("LEA") && currentT.term.var != -1) {
				result.put(currentT.term.var, thePartialDev);
			}
			
			//pop
			queIndex ++;
		}
		
		for(int i = 0; i < varVal.size(); i ++){
			if(!result.containsKey(i)){
				delta.add(0.0);
			}
			else{
				delta.add(result.get(i));
			}
		}
		
		//PrintDev(que.get(0), partialDev, new HashMap<TreeExp, Boolean>());
		
	}
	
	
	
	//Get gradient expression of this expression
	//It is a process of building numOfVar trees
	public double GetGradient(int var, ArrayList<Double> varVal, HashMap<TreeExp, Double> gradRec, HashMap<TreeExp, Double> valRec) throws EvalException{
		if(gradRec.containsKey(this)){
			return gradRec.get(this);
		}
		double r = 0;
		if (expType.equals("LEA")) {
			r = GetGradientForTerm(var);
		} else {
			if (expType.equals("PRO")) {
				for (int t = 0; t < subExp.size(); t++) {
					double tmp = 1;
					for(int tt = 0; tt < subExp.size(); tt++){
						tmp *= tt == t? subExp.get(tt).GetGradient(var, varVal, gradRec, valRec) : 
							subExp.get(tt).RealValue(varVal, valRec);
						if(tmp == 0){
							break;
						}
					}
					r += tmp;
				}
			} else {
				if (expType.equals("MIN")) {
					r = subExp.get(0).GetGradient(var, varVal, gradRec, valRec);
					for (int t = 1; t < subExp.size(); t++) {
						r -= subExp.get(t).GetGradient(var, varVal, gradRec, valRec);
					}

				} else {
					if (expType.equals("SUM")) {
						for (int t = 0; t < subExp.size(); t++) {
							r += subExp.get(t).GetGradient(var, varVal, gradRec, valRec);
						}
					} else {
						if (expType.equals("DIV")) {
							if (subExp.size() != 2) {
								throw new EvalException(
										"Divid has to have twoo subexps!");
							}
							r = subExp.get(0).GetGradient(var, varVal, gradRec,
									valRec)
									* subExp.get(1).RealValue(varVal, valRec)
									- subExp.get(1).GetGradient(var, varVal,
											gradRec, valRec)
									* subExp.get(0).RealValue(varVal, valRec);
							r /= Math.pow(
									subExp.get(1).RealValue(varVal, valRec), 2);
						} else {
							throw new EvalException(
									"GetGradient: Can only SUM/PRO/MIN appears in Q tree!");
						}
					}
				}
			}
		}	

		gradRec.put(this, r);
		return r;
	}
	
	public double ToNumber(){
		if(expType.equals("LEA") && term.var == -1){
			return term.coefficient;
		}
		else{
			return Double.NaN;
		}
	}
	
	public TreeExp ADD(TreeExp another){
		double thisD = this.ToNumber();
		double d = another.ToNumber();
		//if any addent is 0 simply return the other one
		if (!Double.isNaN(thisD) && thisD == 0) {
			return another;
		} else {
			if (!Double.isNaN(d) && d == 0) {
				return this;
			} else {
				//if the two addent are both numbers, just add them
				if(!Double.isNaN(d) && !Double.isNaN(thisD)){
					
					return new TreeExp(thisD + d, null);
				}
				else{
					// if this is already a sum node 
					if (expType.equals("SUM") && father == null) {
						
						subExp.add(another);
						if (another.father == null) {
							another.father = new ArrayList<TreeExp>();
						}
						another.father.add(this);
						return this;
						
					} else {
						TreeExp newExp = new TreeExp("SUM", null);
						newExp.subExp.add(this);
						newExp.subExp.add(another);
						if (another.father == null) {
							another.father = new ArrayList<TreeExp>();
						}
						another.father.add(newExp);
						if (father == null) {
							father = new ArrayList<TreeExp>();
						}
						father.add(newExp);
						return newExp;
					}
				}
				
				
			}
		}
	}
	
	public TreeExp MINUS(TreeExp another){
		double thisD = this.ToNumber();
		double d = another.ToNumber();

		if (!Double.isNaN(d) && d == 0) {
			return this;
		} else {
			// if the two addent are both numbers, just add them
			if (!Double.isNaN(d) && !Double.isNaN(thisD)) {
				return new TreeExp(thisD - d, null);
			} else {
				if (expType.equals("MIN") && father == null) {
					
					subExp.add(another);
					if (another.father == null) {
						another.father = new ArrayList<TreeExp>();
					}
					another.father.add(this);
					return this;
					
				} else {
					TreeExp newExp = new TreeExp("MIN", null);
					newExp.subExp.add(this);
					newExp.subExp.add(another);
					if (another.father == null) {
						another.father = new ArrayList<TreeExp>();
					}
					another.father.add(newExp);
					if (father == null) {
						father = new ArrayList<TreeExp>();
					}
					father.add(newExp);
					return newExp;
				}
			}
		}
	}
	
	public TreeExp TIMES(TreeExp another){
		double thisD = this.ToNumber();
		double d = another.ToNumber();
		if((!Double.isNaN(d) && d == 0) || (!Double.isNaN(thisD) && thisD == 0)){
			return new TreeExp(0.0, null);
		}
		else{
			if((!Double.isNaN(d) && d == 1)){
				return this;
			}
			else{
				if((!Double.isNaN(thisD) && thisD == 1)){
					return another;
				}
				else{
					if(!Double.isNaN(thisD) && !Double.isNaN(d)){
						return new TreeExp(thisD * d, null);
					}
					else{
						if(expType.equals("PRO") && father == null){
							subExp.add(another);
							if(another.father == null){
								another.father = new ArrayList<TreeExp>();
							}
							another.father.add(this);
							return this;
						}
						else{
							TreeExp newExp = new TreeExp("PRO", null);
							newExp.subExp.add(this);
							newExp.subExp.add(another);
							if(another.father == null){
								another.father = new ArrayList<TreeExp>();
							}
							another.father.add(newExp);
							if(father == null){
								father = new ArrayList<TreeExp>();
							}
							father.add(newExp);
							return newExp;
						}
					}
				}
			}
		}
	}
	
	public TreeExp DIVID(TreeExp another){
		double thisD = this.ToNumber();
		double d = another.ToNumber();
		if(!Double.isNaN(thisD) && thisD == 0){
			return new TreeExp(0.0, null);
		}
		else{
			if(!Double.isNaN(d) && d == 1){
				return this;
			}
			else{
				if(!Double.isNaN(d) && d != 0 && !Double.isNaN(thisD)){
					return new TreeExp(thisD / d, null);
				}
				else{
					TreeExp newExp = new TreeExp("DIV", null);
					newExp.subExp.add(this);
					newExp.subExp.add(another);
					if(another.father == null){
						another.father = new ArrayList<TreeExp>();
					}
					another.father.add(newExp);
					if(father == null){
						father = new ArrayList<TreeExp>();
					}
					father.add(newExp);
					return newExp;
				}
			}
		}
	}
	
	public int Size(ArrayList<TreeExp> visited){
		
		int r = 0;
		if(visited.contains(this)){
			r = 0;
			return r;
		}
		else{
			if(expType.equals("LEA")){
				r = 1;
			}
			else{
				r = 0;
				for(TreeExp subT: subExp){
					r += subT.Size(visited);
					
				}
				r ++;
			}
		}
		visited.add(this);
		return r;
	}
	
	//Given a list and a node
	//starting from the node, traverse all the noodes that it reaches
	//terminating the search if encountering a node in the list
	//return the list - all reaching nodes
	public void RemoveUsefulSingleLayer(ArrayList<TreeExp> nodes, TreeExp reward){
		//width first search starting from reward
		ArrayList<TreeExp> queue = new ArrayList<TreeExp>();
		ArrayList<TreeExp> visited = new ArrayList<TreeExp>();
		queue.add(reward);
		int index = 0;
		while(index < queue.size()){
			TreeExp head = queue.get(index);
			visited.add(head);
			for(TreeExp child: head.subExp){
				//if the child in already in nodes meaning the search terminates here
				//if a node is already searched no need to search it again
				if(!nodes.contains(child) && !visited.contains(child)){
					queue.add(child);
				}
			}
			index ++;
		}
		//all visited anodes are reachable from reward
		//this means those nodes are useful, remove them from gabage list
		nodes.removeAll(visited);
	}
	
	
	
	public String toString(){
		if (expType.equals("LEA")) {
			if (term.var == -1) {
				return String.valueOf(term.coefficient);
			} else {
				return "v" + String.valueOf(term.var);
			}
		} else {
			if (expType.equals("PRO")) {
				String s = new String();
				s += "(";
				for (TreeExp subT : subExp) {
					s += (subT.toString());
					if (subExp.indexOf(subT) != subExp.size() - 1) {
						s += " ";
					}
				}
				s += ")";
				return "(* " + s + ")";
			} else {
				if (expType.equals("SUM")) {
					String s = new String();
					s += "(";
					for (TreeExp subT : subExp) {
						s += (subT.toString());
						if (subExp.indexOf(subT) != subExp.size() - 1) {
							s += " ";
						}
					}
					s += ")";
					return "(+ " + s + ")";
				} else {
					if (expType.equals("MIN")) {
						String s = new String();
						s += "(";
						for (TreeExp subT : subExp) {
							s += (subT.toString());
							if (subExp.indexOf(subT) != subExp.size() - 1) {
								s += " ";
							}
						}
						s += ")";
						return "(- " + s + ")";
					} else {
						if (expType.equals("DIV")) {
							String s = new String();
							s += "(";
							for (TreeExp subT : subExp) {
								s += (subT.toString());
								if (subExp.indexOf(subT) != subExp.size() - 1) {
									s += " ";
								}
							}
							s += ")";
							return "(/ " + s + ")";
						} else {
							try {
								throw new EvalException("!!!!");
							} catch (EvalException e) {
								// TODO Auto-generated catch block
								e.printStackTrace();
							}
						}
					}
				}
			}
			
		}
		return new String();
	}
}


