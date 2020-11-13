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
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.core.featurehouse.proofautomation.configuration.Configuration;
import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.DefaultStrategies;
import de.ovgu.featureide.core.featurehouse.proofautomation.keyAE.AbstractContract;
import de.ovgu.featureide.core.featurehouse.proofautomation.keyAE.AbstractExecution;
import de.ovgu.featureide.core.featurehouse.proofautomation.keyAE.KeyHandler;
import de.ovgu.featureide.core.featurehouse.proofautomation.keyAE.ProofHandler;
import de.ovgu.featureide.core.featurehouse.proofautomation.statistics.ProofInformation;

/**
 * TODO description
 * 
 * @author marlen
 */
public class Metaproduct extends AbstractVerification{
	private int maxRuleApplication = Configuration.maxRuleApplication; // sets the maximal number of rules to be applicated on one proof
	KeyHandler keyHandler;
	public static final Metaproduct METAPRODUCT = new Metaproduct();
	
	public static Metaproduct getInstance() {
		return METAPRODUCT;
	}
	/**
	 * Performs the evaluation
	 * @param loc
	 */
	public void performVerification(File loc, File evalPath){
		//Phase 1
				String savePartialProofsPath = evalPath.getAbsolutePath()+FILE_SEPERATOR+FileManager.partialProofsDir;
				boolean firstVersion =loc.getName().contains("1");
				if(!firstVersion){
					File version1 = new File(FileManager.getProjectv1Path(evalPath).getAbsolutePath()+FILE_SEPERATOR+FileManager.partialProofsDir);
					FileManager.copyFolderContent(version1,new File(savePartialProofsPath));
				}
				File metaproduct = getMetaproduct(loc);
				List<ProofHandler> abstractProofs = KeyHandler.loadInKeY(metaproduct);
				setphase1ProofList(abstractProofs);
				List<File> abstractProofPart = new LinkedList<File>();
				if(verificationType == "AbstractContract") {
					keyHandler = new AbstractContract();
				}else if(verificationType == "AbstractExecution") {
					keyHandler = new AbstractExecution();
				}
				
				for(ProofHandler a : abstractProofs){
					try {
						File reuseProof = null;
						if(!firstVersion){
							reuseProof = this.proofAlreadyExistsAbstract(a,evalPath);
						}
						if(reuseProof!=null){
							abstractProofPart.add(reuseProof);
						}
						else{
							keyHandler.startAbstractProof(a,maxRuleApplication, DefaultStrategies.defaultSettingsForFeatureStub());
							abstractProofPart.add(a.saveProof(savePartialProofsPath));
						}
					} catch (Exception e) {
						e.printStackTrace();
					}
				}
				
				for(File absProof: abstractProofPart) {
					System.out.println("[" + absProof.getName() + " ("+absProof.getAbsolutePath()+")]");
				}
				
				//Phase 2
				List<ProofHandler> metaproductProofs = KeyHandler.loadInKeY(metaproduct);
				setProofList(metaproductProofs);
				String metaproductPath = evalPath.getAbsolutePath()+FILE_SEPERATOR+FileManager.finishedProofsDir;
				for(ProofHandler a : metaproductProofs){
					String defaultName= a.getTypeName()+"__"+a.getTargetName();
					defaultName = defaultName.replace(" ", "");
					File reuse = null;
					ProofHandler reuseProof = null;
					for(File absProof: abstractProofPart){
						String name = absProof.getName();
						if(name.contains(defaultName)){
							reuse = absProof;
						}
						for(ProofHandler ap : abstractProofs){
							if(ap.getTargetName().equals(a.getTargetName())&&ap.getTypeName().equals(a.getTypeName())){
								reuseProof = ap;
							}
						}
						if(reuse != null)
							System.out.println(defaultName + ": reuse " + reuse.getName() + " ("+reuse.getAbsolutePath()+")");
						else
							System.out.println(defaultName + ": not reused... no file");
					}
					try {
						keyHandler.startMetaProductProof(a,reuse,DefaultStrategies.defaultSettingsForMetaproduct(),maxRuleApplication,metaproductPath);
						if(!a.isClosed()){
							a.removeProof();
							keyHandler.startAbstractProof(a,maxRuleApplication, DefaultStrategies.defaultSettingsForFeatureStub());

							File restartProof = a.saveProof(savePartialProofsPath);
							keyHandler.startMetaProductProof(a,restartProof,DefaultStrategies.defaultSettingsForMetaproduct(),maxRuleApplication,metaproductPath);
						}

						a.saveProof(metaproductPath);
						ProofInformation aTotal = new ProofInformation(a.getTypeName(),
								a.getTargetName(),a.getFeaturestub(),a.getStat(),a.getReusedStat(),a.isClosed());
						if(reuseProof!=null){
							aTotal.getStat().addStatistics(reuseProof.getStat());
							aTotal.getReusedStat().addStatistics(reuseProof.getReusedStat());
						}
						proofListWithPhase1And2.add(aTotal);
						
					} catch (Exception e) {
						e.printStackTrace();
					}
				}
	}
}
