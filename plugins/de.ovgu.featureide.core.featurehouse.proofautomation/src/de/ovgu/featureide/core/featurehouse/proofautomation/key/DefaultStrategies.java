/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.core.featurehouse.proofautomation.key;

import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.strategy.StrategyProperties;

/**
 * Contains the strategy sets for the different approaches in key
 * 
 * @author Stefanie
 */
public class DefaultStrategies {
	/**
	 * Prepares the StrategyPropertys as used for FeatureStub Verification
	 * @return The prepared StrategyProperties
	 * 
	 * [StrategyProperty]OSS_OPTIONS_KEY=OSS_OFF

[Choice]DefaultChoices=  
runtimeExceptions-runtimeExceptions\\:allow , 
JavaCard-JavaCard\\:off , 
permissions-permissions\\:off , 
moreSeqRules-moreSeqRules\\:off , 
mergeGenerateIsWeakeningGoal-mergeGenerateIsWeakeningGoal\\:off , 
javaLoopTreatment-javaLoopTreatment\\:efficient , 
methodExpansion-methodExpansion\\:modularOnly

[StrategyProperty]INF_FLOW_CHECK_PROPERTY=INF_FLOW_CHECK_FALSE
[SMTSettings]invariantForall=false
[StrategyProperty]BLOCK_OPTIONS_KEY=BLOCK_CONTRACT_INTERNAL
[StrategyProperty]QUERY_NEW_OPTIONS_KEY=QUERY_ON
[Labels]UseOriginLabels=true
[StrategyProperty]MPS_OPTIONS_KEY=MPS_MERGE
[StrategyProperty]STOPMODE_OPTIONS_KEY=STOPMODE_NONCLOSE
	 */
	public static StrategyProperties defaultSettingsForFeatureStub(){
		StrategyProperties sp = ProofSettings.DEFAULT_SETTINGS.getStrategySettings().getActiveStrategyProperties();
		sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY, StrategyProperties.QUERY_ON);
		sp.setProperty(StrategyProperties.QUERYAXIOM_OPTIONS_KEY, StrategyProperties.QUERYAXIOM_OFF);		
		sp.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY, StrategyProperties.STOPMODE_NONCLOSE);
		sp.setProperty(StrategyProperties.SPLITTING_OPTIONS_KEY, StrategyProperties.SPLITTING_DELAYED);
		sp.setProperty(StrategyProperties.LOOP_OPTIONS_KEY, StrategyProperties.LOOP_INVARIANT);
		sp.setProperty(StrategyProperties.BLOCK_OPTIONS_KEY, StrategyProperties.BLOCK_CONTRACT_INTERNAL);
		sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, StrategyProperties.METHOD_CONTRACT);
		sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY, StrategyProperties.DEP_OFF);
		sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_DEF_OPS);
		sp.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY, StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS);
		sp.setProperty(StrategyProperties.CLASS_AXIOM_OPTIONS_KEY, StrategyProperties.CLASS_AXIOM_DELAYED);
		sp.setProperty(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY, StrategyProperties.AUTO_INDUCTION_OFF);
		sp.setProperty(StrategyProperties.OSS_OPTIONS_KEY,StrategyProperties.OSS_OFF);
		return sp;
	}
	
	/**
	 * Prepares the StrategyPropertys as used for Metaproduct Verification in VA1 VA2 and VA3
	 * @return The prepared StrategyProperties
	 */	
	public static StrategyProperties defaultSettingsForMetaproduct(){
		StrategyProperties sp = ProofSettings.DEFAULT_SETTINGS.getStrategySettings().getActiveStrategyProperties();
		sp.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY, StrategyProperties.STOPMODE_NONCLOSE);
		sp.setProperty(StrategyProperties.SPLITTING_OPTIONS_KEY, StrategyProperties.SPLITTING_DELAYED);
		sp.setProperty(StrategyProperties.LOOP_OPTIONS_KEY, StrategyProperties.LOOP_INVARIANT);
		sp.setProperty(StrategyProperties.BLOCK_OPTIONS_KEY, StrategyProperties.BLOCK_CONTRACT_EXTERNAL);
		sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, StrategyProperties.METHOD_CONTRACT);
		sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY, StrategyProperties.DEP_ON);
		sp.setProperty(StrategyProperties.QUERYAXIOM_OPTIONS_KEY, StrategyProperties.QUERYAXIOM_OFF);
		sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_DEF_OPS);
		sp.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY, StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS);
		sp.setProperty(StrategyProperties.CLASS_AXIOM_OPTIONS_KEY, StrategyProperties.CLASS_AXIOM_DELAYED);
		sp.setProperty(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY, StrategyProperties.AUTO_INDUCTION_OFF);
			
		sp.remove(StrategyProperties.SYMBOLIC_EXECUTION_ALIAS_CHECK_OPTIONS_KEY);
		sp.remove(StrategyProperties.SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OPTIONS_KEY);
		
		sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY, StrategyProperties.QUERY_ON);
		
		sp.setProperty(StrategyProperties.OSS_OPTIONS_KEY,StrategyProperties.OSS_OFF);
		return sp;
	}
	
	/**
	 * Prepares the StrategyPropertys as used for Method Inlining and Thuem et al.
	 * @return The prepared StrategyProperties
	 */
	public static StrategyProperties defaultSettingsForVA4VA5(){
		StrategyProperties sp = ProofSettings.DEFAULT_SETTINGS.getStrategySettings().getActiveStrategyProperties();
		sp.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY, StrategyProperties.STOPMODE_DEFAULT);
		sp.setProperty(StrategyProperties.SPLITTING_OPTIONS_KEY, StrategyProperties.SPLITTING_DELAYED);
		sp.setProperty(StrategyProperties.LOOP_OPTIONS_KEY, StrategyProperties.LOOP_EXPAND);
		sp.setProperty(StrategyProperties.BLOCK_OPTIONS_KEY, StrategyProperties.BLOCK_EXPAND);
		sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, StrategyProperties.METHOD_EXPAND);
		sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY, StrategyProperties.DEP_ON);
		sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY, StrategyProperties.QUERY_ON);
		sp.setProperty(StrategyProperties.QUERYAXIOM_OPTIONS_KEY, StrategyProperties.QUERYAXIOM_ON);
		sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_DEF_OPS);
		sp.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY, StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS);
		sp.setProperty(StrategyProperties.CLASS_AXIOM_OPTIONS_KEY, StrategyProperties.CLASS_AXIOM_FREE);
		sp.setProperty(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY, StrategyProperties.AUTO_INDUCTION_OFF);
		sp.remove(StrategyProperties.SYMBOLIC_EXECUTION_ALIAS_CHECK_OPTIONS_KEY);
		sp.remove(StrategyProperties.SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OPTIONS_KEY);
		
		sp.setProperty(StrategyProperties.OSS_OPTIONS_KEY,StrategyProperties.OSS_OFF);
		return sp;
	}
	

}
