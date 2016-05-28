package rddl.policy;

import java.lang.reflect.Array;

import rddl.competition.Records;

import java.security.AllPermission;
import java.util.*;

import javax.naming.InitialContext;
import javax.xml.soap.SAAJMetaFactory;

import org.apache.xerces.impl.xpath.XPath.Step;

import rddl.TreeExp;
import rddl.TEState;
import rddl.EvalException;
import rddl.RDDL;
import rddl.RDDL.*;
import rddl.State;
import rddl.parser.parser;
import rddl.viz.GenericScreenDisplay;
import rddl.viz.NullScreenDisplay;
import rddl.viz.StateViz;
import rddl.RDDL.INSTANCE;
import rddl.RDDL.ENUM_TYPE_DEF;
import rddl.RDDL.LCONST;
import rddl.RDDL.LVAR;
import rddl.RDDL.PVARIABLE_DEF;
import rddl.RDDL.PVAR_INST_DEF;
import rddl.RDDL.PVAR_NAME;
import util.Permutation;

public class a1 extends Policy {
	
	public a1 () { 
		super();
	}
	
	public a1(String instance_name) {
		super(instance_name);
	}
	
	//const for random policy
	double randomAction = 1.0 / 2;
	//double alpha = 0.00001;
	//convergence threashold
	//this is just init value. it will be adjusted by another par
	double ConvergeT = 0.0001;
	
	//the portion of time spent on sampling final actions, given the marginal prob of each bit
	final double SampleTime = 0.2;
	//how many times do we wanna update each action bit
	final int numOfIte = 30;
	//the depth of variables that we reach
	//this is dynamic
	int maxVarDepth = 0;
	long t0 = 0;
	//final int iterationTime = 10;
	int countActBits = 0;
	//if time out
	boolean stopAlgorithm = false;
	//int counter;
	//if use multi layer vars
	boolean ifMultiLayer = false;
	//min number of varibales
	final int baseVarNum = 200;
	//base number of dived the alpha legal region
	final int AlphaTime = 10;
	//if record the tree
	final boolean ifRecord = false;
	//oldQ * this = ConvergeT
	final double RelativeErr = 0.0001;

	//max time of iteratively shrink alpha
	final int MaxShrink = 5;
	//when we go beyond legal region, do we project back by
	//decreasing the same value for all vars or by times a factor
	final boolean ifProjectwtTime = false;
	
	final boolean ifPrint = true;
	final boolean ifPrintBit = false;
	boolean ifPrintProb = false;
	//print out the starting and ending points of each random restart
	boolean ifPrintGrid = false;
	
	//specially for elevator
	boolean ifOldEle = false;
	boolean ifNewEle = false;
	
	//if use forward accumulation or reverse accumulation
	boolean ifReverseAccu = false;
	
	//build the reward expectation function
	// with only the root level actions as variable
	// the other levels actions are treated as constant
	
	TreeExp BuildF(State s) throws EvalException{
		// final F function
		INSTANCE instance = rddl._tmInstanceNodes.get(_instanceName);
		DOMAIN domain = rddl._tmDomainNodes.get(instance._sDomain);
		double cur_discount = 1;
		
		//for each action bit with the first maxVarDepth steps will have a F TExp
		// use action counter to encode each action var
		int actionCounter = 0;
		HashMap<Integer, HashMap<PVAR_NAME, HashMap<ArrayList<LCONST>, TreeExp>>> actions = new HashMap<Integer, HashMap<PVAR_NAME, HashMap<ArrayList<LCONST>, TreeExp>>>();
		for (int h = 0; h <= maxVarDepth; h++) {
			actions.put(h, new HashMap<PVAR_NAME, HashMap<ArrayList<LCONST>, TreeExp>>());
			for (PVAR_NAME p : s._alActionNames) {
				actions.get(h).put(p, new HashMap<ArrayList<LCONST>, TreeExp>());
				ArrayList<ArrayList<LCONST>> terms = s.generateAtoms(p);
				for (ArrayList<LCONST> t : terms) {
					
						actions.get(h).get(p).put(t, new TreeExp((Integer)actionCounter, null));

					actionCounter ++;
				}
			}
		}

		// Q function
		TreeExp F = new TreeExp(0.0, null);

		// initialize
		TEState as = new TEState();
		State cs = new State();
		cs = (State)DeepCloneUtil.deepClone(s);
		as.init(cs);
		
		//this is the "actionProb" used to estimate average time consuming for one iteration
		//because it needs to be used at each step, prepare it here
		ArrayList<Double> varVal = new ArrayList<Double>();
		for(int i = 0; i < countActBits * (maxVarDepth + 1); i ++){
			varVal.add(_random.nextDouble());
		}

		//push forward until time estimate ilustrats that we cannot push more
		int maxDepth = (instance._nHorizon - currentRound)  > instance._nHorizon ? instance._nHorizon : (instance._nHorizon - currentRound);
		int h = 0;
		for (; h < maxDepth; h++) {
			//actions
			ArrayList<PVAR_INST_DEF> trajeActs = new ArrayList<RDDL.PVAR_INST_DEF>();
			// check time
			if ((System.currentTimeMillis() - t0) > _timeAllowed ) {
				break;
			}
			if(h <= maxVarDepth){
				for (PVAR_NAME p : as._alActionNames) {
					for (ArrayList<LCONST> t : as.generateAtoms(p)) {
						trajeActs.add(new PVAR_INST_DEF(p._sPVarName,
								(Object) actions.get(h).get(p).get(t), t));
					}
				}
			}
			else{
				for (PVAR_NAME p : as._alActionNames) {
					for (ArrayList<LCONST> t : as.generateAtoms(p)) {
						trajeActs.add(new PVAR_INST_DEF(p._sPVarName,
								(Object)new TreeExp((Double)randomAction, null), t));
					}
				}
			}	
			as.computeNextState(trajeActs, _random);
			TreeExp reward = as.toTExp(domain._exprReward.sample(new HashMap<LVAR, LCONST>(), as, _random), null);
			F = (TreeExp)RDDL.ComputeArithmeticResult(F, RDDL.ComputeArithmeticResult(reward, cur_discount, "*"), "+");
			
			if(ifRecord){
				Records r = new Records();
				r.fileAppend("BUIlding2", "-state-\n");
				for (PVAR_NAME p : as._alStateNames) {
					for (ArrayList<LCONST> t : as.generateAtoms(p)) {
						r.fileAppend("BUIlding2", p._sPVarName + t.toString() + as.getPVariableAssign(p, t).toString() + "\n");
					}
				}
				
				r.fileAppend("BUIlding2", "-reward-\n");
				r.fileAppend("BUIlding2", reward.toString() + "\n");
				r.fileAppend("BUIlding2", "-F-\n");
				r.fileAppend("BUIlding2", F.toString() + "\n");
			}
			
			
			as.advanceNextState();
			
			cur_discount *= instance._dDiscount;
			// output the current achieved depth
			if(ifPrint){
				System.out.println("finish: " + h + " steps.");
			}
			
			
			//try three times of update
			if(countActBits >= 3){
				
				HashMap<TreeExp, Double> gradRec = new HashMap<TreeExp, Double>();
				HashMap<TreeExp, Double> valRec = new HashMap<TreeExp, Double>();
				long t00 = System.currentTimeMillis();
				F.GetGradient(0, varVal, gradRec, valRec);
				F.GetGradient(1, varVal, gradRec, valRec);
				F.GetGradient(2, varVal, gradRec, valRec);
				long t11 = System.currentTimeMillis();
				//if by estimate, the total time for doing numOfIte times of updates is more than 90% of time left
				//stop, because this mean if we push forward more, we will have no time to finish iterations
				double estimateAvgIte = (t11 - t00) / 3;
				long timeLeft = (long)(_timeAllowed * 0.6) - (t11 - t0);
				int estLayer = h < maxVarDepth ? h : maxVarDepth;
				if( estimateAvgIte * countActBits * (estLayer + 1) * numOfIte > timeLeft * 0.9){
					System.out.println("Estimate time for each iteration: " + estimateAvgIte + ", and we will have " + ((estLayer + 1) * numOfIte) + ", while time allowed is: " + timeLeft);
					//for consistency
					h ++;
					break;
				}
			}
		}
		h --;
		if(maxVarDepth > h){
			maxVarDepth = h;
		}
		if(ifPrint)
		System.out.println("We are finally using " + maxVarDepth + "-layer variables");
		
		//int a = F.Size(new ArrayList<TExp>());
		return F;
	}
	
	//arbitarily search over legal region of alpha
	//use the best step length
	public double FndAlpha(State s, TreeExp F, ArrayList<Double> actionProb, ArrayList<Double> delta) throws EvalException{
		double maxAlpha = Double.MAX_VALUE;
		//we allow actionprob to go beyond 1
		//so first find the max prob and then acrrordingly find the space
		double maxProb = -1;
		for(double a: actionProb){
			if(a > maxProb){
				maxProb = a;
			}
		}
		maxProb += 1;
		//traverse each bit to shrink maxalpha
		for(int i = 0; i < actionProb.size(); i ++){
			double possibleAlpha = -1;
			if(delta.get(i) > 0){
				possibleAlpha = (maxProb-actionProb.get(i)) / Math.abs(delta.get(i));
			}
			if(delta.get(i) < 0){
				possibleAlpha = (actionProb.get(i) - (-1)) / Math.abs(delta.get(i));
			}
			if(possibleAlpha != -1 && possibleAlpha < maxAlpha){
				maxAlpha = possibleAlpha;
			}
		}
		//if we do concurrency projection then we need to again shrink the alpha by constraint the sum of prob be no bigger than
		//concurrency
		

		
		//System.out.println("max alpha is: " + maxAlpha);
		//now try alpha from 0 to maxAlpha
		double bestAlpha = 0;
		double bestQ = Double.NEGATIVE_INFINITY;
		ArrayList<Double> tempActProb = new ArrayList<Double>();
		for(int i = 0; i < actionProb.size(); i ++){
			tempActProb.add(0.0);
		}
		ArrayList<Double> bestActProb = new ArrayList<Double>();
		for(int i = 0; i < actionProb.size(); i ++){
			bestActProb.add(0.0);
		}
		//try to find the alpha with highest Q
		double realBest = -1;
		//this is a loop to find smallest alpha because too large alpha could be a problem
		//if we find in one iteration alpha is chosen to be the smallest among possible then we extend another "alphatime"
		//between 0 and the smallest
		//maxAlpha = 0.2;
		int shrinkCounter = 0;
		
		bestAlpha = 1;
				//System.out.println(bestAlpha);
				//update temp actprob
				for(int j = 0; j < actionProb.size(); j ++){
					
					double d = delta.get(j);

					double newVal = actionProb.get(j) + bestAlpha * d;
					if(newVal < 0){
						newVal = 0;
					}
					if(newVal > 1){
						newVal = 1;
					}

					tempActProb.set(j, newVal);
				}

				
				Projection(s._nMaxNondefActions, tempActProb);
				
				

						//update actionProb
						for(int j = 0; j < actionProb.size(); j ++){
							bestActProb.set(j, tempActProb.get(j));
						}

		
		
		for(int j = 0; j < actionProb.size(); j ++){
			actionProb.set(j, bestActProb.get(j));
		}
		HashMap<TreeExp, Double> valRec = new HashMap<TreeExp, Double>();
		return F.RealValue(actionProb, valRec);
	}
	
	public void ProjectionByList(double sumLimit, ArrayList<Double> actionProb){
		int morethan1Counter = 0;
		
		//used to do hueristically projection
		double sumOfProb = 0;
		//max of all action prob
		//also used for hueristical projection
		double maxOfProb = Double.NEGATIVE_INFINITY;
		
		for(int j = 0; j < actionProb.size(); j ++){
			int currentDepth = j / countActBits;
			double newVal = actionProb.get(j);
			morethan1Counter ++;
			//update sum to do projection
			sumOfProb += newVal;
			if(newVal > maxOfProb){
				maxOfProb = newVal;
			}
			
		}
		//do projection
		for(int h = 0; h <= maxVarDepth; h ++){
			double sumP = sumOfProb;

			double adjustPar = Double.NaN;
			if(sumP > sumLimit){
				if(ifProjectwtTime){
					adjustPar = sumLimit / sumP;
					for(int j = 0; j < countActBits; j ++){
						actionProb.set(h * countActBits + j, actionProb.get(h * countActBits + j) * adjustPar);
					}
				}
				else{
					adjustPar = sumP - sumLimit;
					double theRemain = adjustPar;
					int notZero = 0;
					for(int j = 0; j < actionProb.size(); j ++){
						double theVal = actionProb.get(j);
						if(theVal > 0){
							notZero ++;
						}
					}
					while(theRemain > 0){
						double del = theRemain / notZero;
						theRemain = 0;
						notZero = 0;
						for(int j = 0; j < actionProb.size(); j ++){
							double oldVal = actionProb.get(j);
							if(oldVal == 0){
								continue;
							}
							double newVal = oldVal - del;
							actionProb.set(j, newVal < 0 ? 0 : newVal);
							if(newVal < 0){
								theRemain -= newVal;
							}
							if(newVal > 0){
								notZero ++;
							}
						}
					}
				}
			}

				
			
		}
	}
	
	public void Projection(int concurrency, ArrayList<Double> actionProb){
		
		
		ArrayList<Integer> morethan1Counter = new ArrayList<Integer>();
		for(int j = 0; j <= maxVarDepth; j ++){
			morethan1Counter.add(0);
		}
		//used to do hueristically projection
		ArrayList<Double> sumOfProb = new ArrayList<Double>();
		for(int j = 0; j <= maxVarDepth; j ++){
			sumOfProb.add(0.0);
		}
		//max of all action prob
		//also used for hueristical projection
		ArrayList<Double> maxOfProb = new ArrayList<Double>();
		for(int j = 0; j <= maxVarDepth; j ++){
			maxOfProb.add(Double.NEGATIVE_INFINITY);
		}
		for(int j = 0; j < actionProb.size(); j ++){
			int currentDepth = j / countActBits;
			double newVal = actionProb.get(j);
			if(newVal > 1){
				morethan1Counter.set(currentDepth, morethan1Counter.get(currentDepth)+1);
			}
			//update sum to do projection
			sumOfProb.set(currentDepth, sumOfProb.get(currentDepth) + newVal);
			if(newVal > maxOfProb.get(currentDepth)){
				maxOfProb.set(currentDepth, newVal);
			}
			
		}
		//do projection
		for(int h = 0; h <= maxVarDepth; h ++){
			
			//************This is for elevator use*************//
			if(ifOldEle || ifNewEle){
				int numOfAct = 0;
				if(ifOldEle){
					numOfAct = 3;
				}
				if(ifNewEle){
					numOfAct = 4;
				}
				for(int i = 0; i < concurrency; i ++){
					ArrayList<Double> eleList = new ArrayList<Double>();
					for(int j = 0; j < numOfAct; j ++){
						eleList.add(actionProb.get(h * countActBits + i+j*concurrency));
						
					}
					ProjectionByList(1, eleList);
					for(int j = 0; j < numOfAct; j ++){
						actionProb.set(h * countActBits + i+j*concurrency, eleList.get(j));
						
					}
				}
				
				
			}
			
			//*********ele use end here********************//
			
			double sumP = sumOfProb.get(h);

			double adjustPar = Double.NaN;
			if(sumP > concurrency){
				if(ifProjectwtTime){
					adjustPar = concurrency / sumP;
					for(int j = 0; j < countActBits; j ++){
						actionProb.set(h * countActBits + j, actionProb.get(h * countActBits + j) * adjustPar);
					}
				}
				else{
					adjustPar = sumP - concurrency;
					double theRemain = adjustPar;
					int notZero = 0;
					for(int j = 0; j < countActBits; j ++){
						double theVal = actionProb.get(h * countActBits + j);
						if(theVal > 0){
							notZero ++;
						}
					}
					while(theRemain > 0){
						double del = theRemain / notZero;
						theRemain = 0;
						notZero = 0;
						for(int j = 0; j < countActBits; j ++){
							double oldVal = actionProb.get(h * countActBits + j);
							if(oldVal == 0){
								continue;
							}
							double newVal = oldVal - del;
							actionProb.set(h * countActBits + j, newVal < 0 ? 0 : newVal);
							if(newVal < 0){
								theRemain -= newVal;
							}
							if(newVal > 0){
								notZero ++;
							}
						}
					}
				}
			}
		
				
			
		}
		
		
		
		
		
	}
	
	

	public ArrayList<Double> UpdateAllwtProj(State s, TreeExp F) throws EvalException{

		ArrayList<Double> actionProb = new ArrayList<Double>();
		for(int i = 0; i < countActBits * (maxVarDepth + 1); i ++){
			actionProb.add(0.0);
		} 
		//ArrayList<TExp> visited = new ArrayList<TExp>();
		//int b = F.Size(visited );
		//iteration counter
		int randomRestart = 0;
		//Record the best actionProb that gets the highest Q value in F tree
		ArrayList<Double> bestActionProb = new ArrayList<Double>();
		for(int i = 0; i < countActBits; i ++){
			bestActionProb.add(0.0);
		}
		double bestQ = Double.NEGATIVE_INFINITY;
		
		int iteCounter = 0;
		while(!stopAlgorithm){
			iteCounter ++;
			//a record of how many times we keep decreasing Q
			//sometims because alpha is too large the Q keeps going down
			//if that happens for enough many times we simply force it to cenverge
			int doDownTimes = 0;
			
			
					for(int i = 0; i < actionProb.size(); i ++){
						actionProb.set(i, _random.nextDouble());
						//actionProb.set(i, 0.5);
						//actionProb.set(i, randomAction);
						
					}
					Projection(s._nMaxNondefActions, actionProb);
					
				
				
			
			if(ifPrintGrid){
				ArrayList<Integer> alreadyIn = new ArrayList<Integer>();
				for(int i = 1; i <= s._nMaxNondefActions; i ++){
					double maxVal = -1;
					int maxJ = -1;
					for(int j = 0; j < actionProb.size(); j ++){
						double val = actionProb.get(j);
						if(alreadyIn.contains(j)){
							continue;
						}
						if(val > maxVal){
							maxVal = val;
							maxJ = j;
						}
					}
					if(maxVal < randomAction){
						break;
					}
					alreadyIn.add(maxJ);
				}
				System.out.print("\n\nSta: ");
				for(int j: alreadyIn){
					System.out.print(j + " ");
				}
			}
			//iteratively update action probs until converge
			boolean ifConverge = false;
			//a value table to record the realvalue of trees
			//only used in one iteration
			//need to be clear after use
			HashMap<TreeExp, Double> valRec = new HashMap<TreeExp, Double>();
			HashMap<TreeExp, Double> gradRec = new HashMap<TreeExp, Double>();
			//initialize oldQ to be realvalue calculated with initial action prob
			double oldQ = F.RealValue(actionProb, valRec);
			if(ifPrint){
				System.out.println("Q is initlaized to: " + oldQ);
			}
			
			//based on this Q value, setup threshold
			ConvergeT = Math.abs(oldQ * RelativeErr);
			//update bestQ and action
			if(oldQ > bestQ){
				bestQ = oldQ;
				for(int a = 0; a < countActBits; a ++){
					bestActionProb.set(a, actionProb.get(a));
				}
			}
			
			//dead bit record
			//if during this random restart, certain bits never change, it means that Q is not related to it
			//set it to be 0
			//only for top level 
			ArrayList<Boolean> ifthisBitChange = new ArrayList<Boolean>();
			for(int a = 0; a < countActBits; a ++){
				ifthisBitChange.add(false);
			}
			if(ifPrintBit){
				System.out.println();
				for(int a = 0; a < actionProb.size(); a++){
					System.out.println("a for " + "v" + a + " " + actionProb.get(a));
				}
				System.out.println();
			}
			//initialize newQ
			double newQ = 0; // this will be recalculated later
			while(!ifConverge && !stopAlgorithm){


				//calculate delta
				ArrayList<Double> delta = new ArrayList<Double>();
				//System.out.println("");
				//this step gets delta for each bit
				if(ifReverseAccu){
					
					F.RevAccGradient(delta, actionProb);
					//System.out.println(gTree.toString());
					if(ifPrintBit){
						for(int i = 0; i < actionProb.size(); i ++){
							System.out.println("d for " + "v" + i + " " + delta.get(i));
						}
					}
					
				}
				else{
					long t000 = System.currentTimeMillis();
					for(int i = 0; i < actionProb.size(); i ++){
						
						double d = F.GetGradient(i, actionProb, gradRec, valRec);
						
						if(ifPrintBit){
							System.out.println("d for " + "v" + i + " " + d);
						}
						
						if(i < countActBits && d != 0){
							ifthisBitChange.set(i, true);
						}
						gradRec.clear();
						delta.add(d);
					}
					//System.out.println(System.currentTimeMillis() - t000);
				}
				
				//this step updates prob and return the Q
				newQ = FndAlpha(s, F, actionProb, delta);
				/*
				if(currentRound == 1){
				for(int i = 0; i < actionProb.size(); i ++){
					actionProb.set(i, 0.0);
				}
				actionProb.set(3, 1.0);
				}
				*/
				if(ifPrintBit){
					for(int a = 0; a < actionProb.size(); a++){
						System.out.println("a for " + "v" + a + " " + actionProb.get(a));
					}
					System.out.println();
				}
				
				
				
				//now alphas are changed so we need to clear the value record in the tree
				valRec.clear();
				
				
				if(ifPrint){
					System.out.println("oldQ: " + oldQ + "\n");
					System.out.println("newQ: " + newQ + "\n");
				}
				
				if(newQ < oldQ){
					doDownTimes ++;
					if(doDownTimes > 1){
						ifConverge = true;
					}
				}
				else{
					doDownTimes = 0;
				}
				if(Math.abs(newQ - oldQ) < ConvergeT){
					ifConverge = true;
				}
				oldQ = newQ;
				//we don't need to clear valrec again
				//because the value when calculating newQ can be reused in next iteration
				if(System.currentTimeMillis() - t0 > _timeAllowed){
					stopAlgorithm = true;
					break;
				}
			}
			if(ifPrintGrid){
				ArrayList<Integer> alreadyIn = new ArrayList<Integer>();
				for(int i = 1; i <= s._nMaxNondefActions; i ++){
					double maxVal = -1;
					int maxJ = -1;
					for(int j = 0; j < actionProb.size(); j ++){
						double val = actionProb.get(j);
						if(alreadyIn.contains(j)){
							continue;
						}
						if(val > maxVal){
							maxVal = val;
							maxJ = j;
						}
					}
					if(maxVal < randomAction){
						break;
					}
					alreadyIn.add(maxJ);
				}
				System.out.print("\nEnd: ");
				for(int j: alreadyIn){
					System.out.print(j + " ");
				}
				
			}
			//converged; continue to next random restart
			randomRestart ++;
			if(ifPrint){
				if(ifConverge){
					System.out.println("RR: " + randomRestart + "converged!");
				}
				else{
					System.out.println("RR: " + randomRestart + "forced to stop because running out of time.");
				}
			}
			//Get the Q value for this convergence
			if(newQ > bestQ){
				if(ifPrint){
					System.out.println("Previous best is: " + bestQ + " and now the Q is: " + newQ);
				}
				
				bestQ = newQ;
				for(int a = 0; a < countActBits; a ++){
					bestActionProb.set(a, actionProb.get(a));
				}
				/*
				System.out.println("Q is updated to: " + newQ); 
				
				System.out.println("Best action prob is updated to: ");
				for(int a = 0; a < countActBits; a ++){
					System.out.println(actionProb.get(a));
				}
				*/
				
			}
			else{
				if(ifPrint){
					System.out.println("Failed to update Q. Previous best is: " + bestQ + " and now the Q is: " + newQ); 
				}
				
			}
			/*
			//if dead bit set to 0
			for(int a = 0; a < countActBits; a ++){
				if(!ifthisBitChange.get(a)){
					bestActionProb.set(a, 0.0);
				}
			}
			*/
		}
		if(ifPrintGrid){
			System.out.println("In total: " + randomRestart);
		}
		//record how many random restart have been done
		_visCounter.randomInTotal += randomRestart;
		
		//printout the action probs
		if(ifPrintBit){
			System.out.println("\nfinal action prob: ");
			for(double a: bestActionProb){
				System.out.println(a);
			}
		}
		System.out.println("best: " + bestQ);
		return bestActionProb;
	}
	
	//sample action from largest to smallest; build actions incrementally
	public ArrayList<PVAR_INST_DEF> SampleAction(HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Double>> actionProb, State conS) throws EvalException{
		ArrayList<PVAR_INST_DEF> finalAction = new ArrayList<RDDL.PVAR_INST_DEF>();
		
		//sample actions based on action prob until getting a legal action

		long t0 = System.currentTimeMillis();
		// check from largest prob to smallest
		boolean ifEnoughAction = false;
		while (System.currentTimeMillis() - t0 <= _timeAllowed * SampleTime) {
			double maxProb = -1;
			PVAR_NAME bestName = null;
			ArrayList<LCONST> bestTerm = null;
			// find the largest prob
			for (PVAR_NAME p : conS._alActionNames) {
				ArrayList<ArrayList<LCONST>> terms = conS.generateAtoms(p);
				for (ArrayList<LCONST> t : terms) {
					if (actionProb.get(p).get(t) > maxProb) {
						maxProb = actionProb.get(p).get(t);
						bestName = p;
						bestTerm = t;
					}
				}
			}
			//every bit has been sampled
			if(bestName == null){
				break;
			}
			// try to sample
			if (_random.nextDouble() <= maxProb) {
				finalAction.add(new PVAR_INST_DEF(bestName._sPVarName, true,
						bestTerm));
				boolean passed_constraints = true;
				try{
					conS.checkStateActionConstraints(finalAction);
				}catch (EvalException e) { 
					// Got an eval exception, constraint violated
					passed_constraints = false;
						//System.out.println(actions + " : " + e);
						//System.out.println(s);
						//System.exit(1);
				} catch (Exception e) { 
					throw new EvalException(e.toString());
				}
				if(!passed_constraints){
					finalAction.remove(finalAction.size()-1);
				}
				
				if (finalAction.size() == conS._nMaxNondefActions) {
					ifEnoughAction = true;
					break;
				}
			}
			actionProb.get(bestName).put(bestTerm, -10.0);
		}
		if(ifEnoughAction){
			System.out.println("we get enough actions.");
		}
		return finalAction;
	}

	//sample action for each bit; until get a legal action or time out (returns noop at that case)
	//last parameter: if always add the bit with largest prob to action list so long as it's legal
	public ArrayList<PVAR_INST_DEF> SampleAction(HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Double>> actionProb, State conS, boolean ifKeeplargest, boolean ifHueristicChoice) throws EvalException{
		if(ifPrintProb){
			for(PVAR_NAME p: conS._alActionNames){
				for(ArrayList<LCONST> t: conS.generateAtoms(p)){
					System.out.println(p._sPVarName+t.toString()+actionProb.get(p).get(t));
				}
			}
		}
		
		//timer
		long t0 = System.currentTimeMillis();
		
		ArrayList<PVAR_INST_DEF> finalAction = new ArrayList<RDDL.PVAR_INST_DEF>();
		
		//if we hueristically choose actions
		//then first sample the number of final actions
		
		int numOfActions = -1;
		if(ifHueristicChoice){
			Random r = new Random();
			//numOfActions = r.nextInt(conS._nMaxNondefActions + 1);
			numOfActions = conS._nMaxNondefActions;
			for(int k = 1; k <= numOfActions; k ++){
				double maxProb = -1;
				PVAR_NAME bestName = null;
				ArrayList<LCONST> bestTerm = null;
		    	for (PVAR_NAME p : conS._alActionNames) {
					ArrayList<ArrayList<LCONST>> terms = conS.generateAtoms(p);
					for (ArrayList<LCONST> t : terms) {
						if (actionProb.get(p).get(t) > maxProb) {
							maxProb = actionProb.get(p).get(t);
							bestName = p;
							bestTerm = t;
						}
					}
				}
				if(maxProb >= randomAction){
					finalAction.add(new PVAR_INST_DEF(bestName._sPVarName, true, bestTerm));
					boolean passed_constraints = true;
					try{
						conS.checkStateActionConstraints(finalAction);
					}catch (EvalException e) { 
						// Got an eval exception, constraint violated
						passed_constraints = false;
							//System.out.println(actions + " : " + e);
							//System.out.println(s);
							//System.exit(1);
					} catch (Exception e) { 
						throw new EvalException(e.toString());
					}
					if(!passed_constraints){
						finalAction.remove(finalAction.size()-1);
					}
					//if succesfully keep the largest, set up its prob to be -10
					else{
						actionProb.get(bestName).put(bestTerm, -10.0);
					}
					if(finalAction.size() == conS._nMaxNondefActions){
						return finalAction;
					}
				}
				else{
					break;
				}
		    }
		}
		else{
			//deal with ifKeepLargest
			if (ifKeeplargest) {
				double maxProb = -1;
				PVAR_NAME bestName = null;
				ArrayList<LCONST> bestTerm = null;
				// find the largest prob
				for (PVAR_NAME p : conS._alActionNames) {
					ArrayList<ArrayList<LCONST>> terms = conS.generateAtoms(p);
					for (ArrayList<LCONST> t : terms) {
						if (actionProb.get(p).get(t) > maxProb) {
							maxProb = actionProb.get(p).get(t);
							bestName = p;
							bestTerm = t;
						}
					}
				}
				if (maxProb >= randomAction) {
					finalAction.add(new PVAR_INST_DEF(bestName._sPVarName,
							true, bestTerm));
					boolean passed_constraints = true;
					try {
						conS.checkStateActionConstraints(finalAction);
					} catch (EvalException e) {
						// Got an eval exception, constraint violated
						passed_constraints = false;
						// System.out.println(actions + " : " + e);
						// System.out.println(s);
						// System.exit(1);
					} catch (Exception e) {
						throw new EvalException(e.toString());
					}
					if (!passed_constraints) {
						finalAction.remove(finalAction.size() - 1);
					}
					// if succesfully keep the largest, set up its prob to be
					// -10
					if (finalAction.size() == 1) {
						actionProb.get(bestName).put(bestTerm, -10.0);
					}
					if (finalAction.size() == conS._nMaxNondefActions) {
						return finalAction;
					}
				}
			}
			
			while(System.currentTimeMillis() - t0 < _timeAllowed * SampleTime){
				//sample each action bit, put them into the final action list
				//finally check if it's legal or not
				for(PVAR_NAME p: conS._alActionNames){
					for(ArrayList<LCONST> t: conS.generateAtoms(p)){
						double dice = _random.nextDouble();
						if(dice < actionProb.get(p).get(t)){
							finalAction.add(new PVAR_INST_DEF(p._sPVarName, true, t));

							//sample actions based on action prob until getting a legal action
							boolean passed_constraints = true;
							try{
								conS.checkStateActionConstraints(finalAction);
							} catch (EvalException e) {
								// Got an eval exception, constraint violated
								passed_constraints = false;
								// System.out.println(actions + " : " + e);
								// System.out.println(s);
								// System.exit(1);
							} catch (Exception e) {
								throw new EvalException(e.toString());
							}
							if (!passed_constraints) {
								finalAction.remove(finalAction.size()-1);
							}
							if(finalAction.size() == conS._nMaxNondefActions){
								return finalAction;
							}
						}
					}
				}
			}
		}
		return finalAction;
	}
	
	//final get action algorithm
	@Override
	public ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException {
		
		//every time get to this point, meaning we have one more time of record of how many random restart have been tried
		_visCounter.randomTime ++;
		
		t0 = System.currentTimeMillis();
		
		// declare a action list
		ArrayList<PVAR_INST_DEF> actions = new ArrayList<RDDL.PVAR_INST_DEF>();
		
		//recalculate the rootinit
		//because we assume there is no constrint so simple use concurrency divided by number of action bits
		if(countActBits == 0){
			for(PVAR_NAME p: s._alActionNames){
				countActBits += s.generateAtoms(p).size();
			}
		}
		
		//adjust maxVarDepth so that maxVarDepth * countActBits > baseVarNum
		maxVarDepth = 0;
		if(ifMultiLayer){
			INSTANCE instance = rddl._tmInstanceNodes.get(_instanceName);
			maxVarDepth = -1;
			while(true){
				maxVarDepth ++;
				if(maxVarDepth == instance._nHorizon || (maxVarDepth + 1) * countActBits >= baseVarNum){
					break;
				}
			}
		}
		
		//counter = 0;
		stopAlgorithm = false;
		
		//the real number of each action bit for taking random policy
		ArrayList<Double> comb = new ArrayList<Double>();
		double numInTotal = 0;

		//caculate the number of choose k from n
		for(int k = 0; k <= s._nMaxNondefActions; k ++){
			int max = countActBits;
			double resu = 1;
			for(int j = 1; j <= k; j ++){
				resu *= max;
				max --;
			}
			for(int j = 2; j <= k; j ++){
				resu /= j;
			}
			//now res the is number of combs (choose j from countActBits)
			comb.add(resu);
			numInTotal += resu;
		}
		//now cal the marginal for random policy
		double marRandom = 0;
		for(int k = 1; k <= s._nMaxNondefActions; k ++){
			marRandom += Double.valueOf(k) / countActBits * comb.get(k) / numInTotal;
		}
		
		for(PVAR_NAME p: s._alActionNames){
			if(p._sPVarName.equals("move-up")){
				marRandom = 0.25;
				ifOldEle = true;
				break;
			}
		}
		
		for(PVAR_NAME p: s._alActionNames){
			if(p._sPVarName.equals("close-door")){
				marRandom = 0.2;
				ifNewEle = true;
				break;
			}
		}
		
		randomAction = marRandom;
		
		//initialize action prob
		ArrayList<Double> actionProb = null;
		
		TreeExp F = BuildF(s);
		
		//update action probs
		actionProb = UpdateAllwtProj(s, F);
		
		//get final action
		HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Double>> probWithName = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Double>>();
		int counter = 0;
		for(PVAR_NAME p: s._alActionNames){
			probWithName.put(p, new HashMap<ArrayList<LCONST>,Double>());
			for(ArrayList<LCONST> t: s.generateAtoms(p)){
				if(p._sPVarName.equals("askProb")){
					@SuppressWarnings("unused")
					int a = 1;
				}
				probWithName.get(p).put(t, actionProb.get(counter));
				counter ++;
			}
		}
		/*
		System.out.println("\nFinally we are using the action probs: ");
		for(PVAR_NAME p: s._alActionNames){
			for(ArrayList<LCONST> t: s.generateAtoms(p)){
				System.out.println(probWithName.get(p).get(t));
			}
		}
		*/
		actions = SampleAction(probWithName, s, false, true);
		return actions;
	}

}
