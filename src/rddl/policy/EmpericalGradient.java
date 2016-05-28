package rddl.policy;

import java.lang.reflect.Array;
import java.security.AllPermission;
import java.util.*;

import javax.naming.InitialContext;
import javax.xml.soap.SAAJMetaFactory;

import org.apache.xerces.impl.xpath.XPath.Step;

import rddl.AState;
import rddl.EState;
import rddl.EvalException;
import rddl.RDDL;
import rddl.RDDL.*;
import rddl.State;
import rddl.parser.parser;
import rddl.viz.GenericScreenDisplay;
import rddl.viz.NullScreenDisplay;
import rddl.viz.StateViz;
import rddl.Expression;
import rddl.RDDL.DOMAIN;
import rddl.RDDL.INSTANCE;
import rddl.RDDL.ENUM_TYPE_DEF;
import rddl.RDDL.LCONST;
import rddl.RDDL.LVAR;
import rddl.RDDL.PVARIABLE_DEF;
import rddl.RDDL.PVAR_INST_DEF;
import rddl.RDDL.PVAR_NAME;
import util.Permutation;

public class EmpericalGradient extends Policy {
	
	public EmpericalGradient () { 
		super();
	}
	
	public EmpericalGradient(String instance_name) {
		super(instance_name);
	}
	
	double rootInit = 0.25;
	final double UnRootAction = 1.0 / 2;
	final double TryStepLen = 0.01;
	final int updateTimes = 10;
	//the portion of time spent on sampling final actions, given the marginal prob of each bit
	final double SampleTime = 0.2;
	
	
	
	//sample action from largest to smallest; build actions incrementally
	public ArrayList<PVAR_INST_DEF> SampleAction(HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Double>> actionProb, State conS) throws EvalException{
		ArrayList<PVAR_INST_DEF> finalAction = new ArrayList<RDDL.PVAR_INST_DEF>();
		
		//sample actions based on action prob until getting a legal action
		boolean passConst = true;
		int countActionBit = 0;
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
				if(maxProb >= rootInit){
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
				if (maxProb >= 0.5) {
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
	
	//update each action bits k times within time millionsecs
	//by emperical gradient
	public long UpdateActionProb(State s, INSTANCE inst, DOMAIN dom, long numOfActionBits, HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Double>> actionProb, double time, ArrayList<PVAR_INST_DEF> unrootAct) throws EvalException{
		ArrayList<PVAR_INST_DEF> initRootAct = new ArrayList<RDDL.PVAR_INST_DEF>();
		for(PVAR_NAME p: s._alActionNames){
			for(ArrayList<LCONST> term: s.generateAtoms(p)){
				initRootAct.add(new PVAR_INST_DEF(p._sPVarName, (Object)actionProb.get(p).get(term), term));
			}	
		}

		
		//first calculate the Q with initial value of all action bits
		//initialize
		double previousQ = 0;
		double accum_reward = 0.0d;
		double cur_discount = 1.0d;
		
		//tempState
		AState as = new AState();
		as.init(s);
		//take one trajectory
		for( int h = 0; h < inst._nHorizon && currentRound + h <= inst._nHorizon; h++ ) {

			as.computeNextState(h == 0? initRootAct : unrootAct, _random);

			double reward = ((Number)dom._exprReward.sample(new HashMap<LVAR,LCONST>(), 
				as, _random)).doubleValue();
			accum_reward += reward * cur_discount;
			cur_discount *= inst._dDiscount;
			as.advanceNextState();
		}
		
		//record the value as previous
		previousQ = accum_reward;
		
		//do for each action bits
		//keep upodating the previousQ and compare new Q with that
		long t0 = System.currentTimeMillis();
		boolean ifBreak = false;
		long countUpdates = 0;
		while(!ifBreak){
			for(PVAR_NAME p: s._alActionNames){
				if(ifBreak){
					break;
				}
				for(ArrayList<LCONST> term: s.generateAtoms(p)){
					if(System.currentTimeMillis() - t0 > time){
						ifBreak = true;
						break;
					}
					
					//try to increase the action bit
					ArrayList<PVAR_INST_DEF> rootAct = new ArrayList<RDDL.PVAR_INST_DEF>();
					for(PVAR_NAME p2: s._alActionNames){
						for(ArrayList<LCONST> terms2: s.generateAtoms(p2)){
							rootAct.add(new PVAR_INST_DEF(p2._sPVarName, p2.equals(p) && terms2.equals(term) 
									? (Object)(actionProb.get(p2).get(terms2)+TryStepLen) : (Object)(actionProb.get(p2).get(terms2)), 
											terms2));
						}	
					}
					
					
					//initialize
					double increasedQ = 0.0d;
					cur_discount = 1.0d;
					
					//tempState
					as = new AState();
					as.init(s);
					//take one trajectory
					for( int h = 0; h < inst._nHorizon && currentRound + h <= inst._nHorizon; h++ ) {

						as.computeNextState(h == 0? rootAct : unrootAct, _random);
						double reward = ((Number)dom._exprReward.sample(new HashMap<LVAR,LCONST>(), 
							as, _random)).doubleValue();
						increasedQ += reward * cur_discount;
						cur_discount *= inst._dDiscount;
						as.advanceNextState();
					}	
					
					//try to decrease the action bit
					rootAct = new ArrayList<RDDL.PVAR_INST_DEF>();
					for(PVAR_NAME p2: s._alActionNames){
						for(ArrayList<LCONST> terms2: s.generateAtoms(p2)){
							rootAct.add(new PVAR_INST_DEF(p2._sPVarName, p2.equals(p) && terms2.equals(term) 
									? (Object)(actionProb.get(p2).get(terms2)-TryStepLen) : (Object)(actionProb.get(p2).get(terms2)), 
											terms2));
						}	
					}
					
					
					//initialize
					double decreasedQ = 0.0d;
					cur_discount = 1.0d;
					
					//tempState
					as = new AState();
					as.init(s);
					//take one trajectory
					for( int h = 0; h < inst._nHorizon && currentRound + h <= inst._nHorizon; h++ ) {

						as.computeNextState(h == 0? rootAct : unrootAct, _random);
						double reward = ((Number)dom._exprReward.sample(new HashMap<LVAR,LCONST>(), 
							as, _random)).doubleValue();
						decreasedQ += reward * cur_discount;
						cur_discount *= inst._dDiscount;
						as.advanceNextState();
					}	
					
					//cpompare new Qs with previousQ
					if(increasedQ > previousQ && increasedQ > decreasedQ){
						actionProb.get(p).put(term, actionProb.get(p).get(term) + TryStepLen);
						previousQ = increasedQ;
					}
					else{
						if(decreasedQ > previousQ && decreasedQ > increasedQ){
							actionProb.get(p).put(term, actionProb.get(p).get(term) - TryStepLen);
							previousQ = decreasedQ;
						}
					}
					countUpdates ++;
				}
			}
		}
		return countUpdates;
	}
	
	//final get action algorithm
	@Override
	public ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException {
		//get instance and domain
		INSTANCE instance = rddl._tmInstanceNodes.get(_sInstanceName);
		DOMAIN domain = rddl._tmDomainNodes.get(instance._sDomain);
		// declare a action list
		ArrayList<PVAR_INST_DEF> actions = new ArrayList<RDDL.PVAR_INST_DEF>();
		EState as = new EState();
		as.init(s);
		
		//action marginal probabilities
		HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Double>> actionProb = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Double>>();
		long countActBits = 0;
		
	
		/*************************************************/
		/*****************individual**********************/
		/*************************************************/
		
		
		long t0 = System.currentTimeMillis();
		//Set up unroot action
		// assume that the random policy is not state dependent
		// get the aggegate action after step 0
		ArrayList<PVAR_INST_DEF> unrootAct = new RandomConcurrentPolicyIndex(s).getAActionDup(s, _timeAllowed * 0.2);
		//initialize the action probs
		rootInit = (Double)unrootAct.get(0)._oValue;
		for (PVAR_NAME p : s._alActionNames) {
			actionProb.put(p, new HashMap<ArrayList<LCONST>, Double>());
			ArrayList<ArrayList<LCONST>> terms = s.generateAtoms(p);
			for (ArrayList<LCONST> t : terms) {
				actionProb.get(p).put(t, rootInit);
				countActBits ++;
			}
		}
		long counts = UpdateActionProb(s, instance, domain, countActBits, actionProb, _timeAllowed * 0.8, unrootAct);
		/*
		for (PVAR_NAME p : s._alActionNames) {
			for (ArrayList<LCONST> t : s.generateAtoms(p)) {
				System.out.println(p._sPVarName + t.toString() + ": "
						+ actionProb.get(p).get(t));
			}
		}
		*/
		//sample action based on the action prob
		actions = SampleAction(actionProb, s, false, true);
		
		return actions;
	}

}
