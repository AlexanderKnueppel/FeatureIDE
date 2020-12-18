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
package de.ovgu.featureide.core.featurehouse.proofautomation.verification;

import java.io.File;
import java.util.List;

import de.ovgu.featureide.core.featurehouse.proofautomation.configuration.Configuration;
import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.DefaultStrategies;
import de.ovgu.featureide.core.featurehouse.proofautomation.key2_7.AbstractContracts;
import de.ovgu.featureide.core.featurehouse.proofautomation.key2_7.DefaultKeY;
import de.ovgu.featureide.core.featurehouse.proofautomation.key2_7.KeyHandler;
import de.ovgu.featureide.core.featurehouse.proofautomation.key2_7.ProofHandler;

/**
 * TODO description
 * 
 * @author marlen
 */
public class MethodInling extends AbstractVerification{
	private int maxRuleApplication = Configuration.maxRuleApplication; // sets the maximal number of rules to be applicated on one proof
	
	public static final MethodInling METHOD_INLING =  new MethodInling();

	public static MethodInling getInstance() {
		return METHOD_INLING;
	}
	
	/**
	 * Performs the evaluation
	 * @param loc
	 */
	public void performVerification(File loc, File evalPath){
		String savePath = evalPath.getAbsolutePath()+FILE_SEPERATOR+FileManager.finishedProofsDir;
		List<ProofHandler> proofList = keyHandler.loadInKeY(FileManager.getFirstMetaproductElement(loc));
		boolean firstVersion = loc.getName().contains("1");
		fullProofReuse(evalPath,proofList,DefaultStrategies.defaultSettingsForVA4VA5(),firstVersion,savePath, keyHandler);
	}
}
