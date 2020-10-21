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
package de.ovgu.featureide.core.featurehouse.proofautomation.keyAE;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.core.featurehouse.proofautomation.builder.MetaProductBuilder;
import de.ovgu.featureide.core.featurehouse.proofautomation.configuration.Configuration;
import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.AutomatingProof;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.DefaultStrategies;

/**
 * TODO description
 * 
 * @author marlen
 */
public class AutomatingProject {
	public static final AutomatingProject automatingProject = new AutomatingProject();
	private List<ProofHandler> proofList = new LinkedList<ProofHandler>();
	private static final String FILE_SEPERATOR = System.getProperty("file.separator");
	private int maxRuleApplication = Configuration.maxRuleApplication;
	
	public void performEval(File loc,File evalPath) {
		String savePartialProofsPath = evalPath.getAbsolutePath()+FILE_SEPERATOR+FileManager.partialProofsDir;
		boolean firstVersion =loc.getName().contains("1");
		if(!firstVersion){
			FileManager.reuseFeaturestub(evalPath, loc);
		}
		performFeaturestubVerification(loc,evalPath,firstVersion, false); //TODO run with false
		FileManager.copySavedProofsToPartialProofs(evalPath);
		MetaProductBuilder.preparePartialProofs(loc,evalPath);
	//	performMetaproductVerification(loc,evalPath);
		
	//	List<ProofHandler> proofs = KeyHandler.loadInKeY(metaproduct);
	//	proofList.addAll(proofs);
	}
	
	
	/**
	 * Returns the first java file of the Metaproduct
	 * @param projectDir
	 * @return
	 */
	private static File getMetaproduct(File projectDir){
		File[] metaproduct = (new File(projectDir.getAbsolutePath()+FILE_SEPERATOR+FileManager.metaproductDir)).listFiles();
		for(File m :metaproduct){
			if(m.getName().endsWith(".java")){
				return m;
			}
		}
		return null;
	}
	
	/**
	 * Performs the featurestub phase of the verification
	 * @param projectDir
	 */
	private void performFeaturestubVerification(File projectDir, File evalPath, boolean firstVersion, boolean stubReplay){
		List<File> featurestubs = FileManager.getAllFeatureStubFilesOfAProject(projectDir);
		String currentFeatureStub;
		String saveFeatureStubPath;
		for(File f: featurestubs){
			String[] seperatedPath = f.getAbsolutePath().split(FILE_SEPERATOR);
			currentFeatureStub = seperatedPath[seperatedPath.length-2];
			saveFeatureStubPath = evalPath.getAbsolutePath()+FILE_SEPERATOR+FileManager.savedProofsDir+FILE_SEPERATOR+currentFeatureStub;
			FileManager.createDir(new File (saveFeatureStubPath));
			List<ProofHandler> ap = KeyHandler.loadInKeY(f);
			proofList.addAll(ap);
			for(ProofHandler a : ap){
				//Replay feature stub proof
				if(firstVersion||!proofAlreadyExists(a,evalPath,f.getParentFile())){
					File oldPartialProof = getOldFeatureStubProof(a, FileManager.getProjectv1Path(projectDir));
					if(!firstVersion && stubReplay && oldPartialProof != null) {
						KeyHandler.startAbstractExcutionProof(a, maxRuleApplication, DefaultStrategies.defaultSettingsForFeatureStub());
						a.saveProof(saveFeatureStubPath);
						a.setFeaturestub(f.getParentFile().getName());
					} else {
						try {
							KeyHandler.startAbstractExcutionProof(a,maxRuleApplication, DefaultStrategies.defaultSettingsForFeatureStub());
							a.saveProof(saveFeatureStubPath);
							a.setFeaturestub(f.getParentFile().getName());
						} catch (Exception e) {
							e.printStackTrace();
						}
					}
				}
			}
		}
	}
	
	/**
	 * Checks if the proof was already copied from a previous version
	 * @param a
	 * @param evalPath
	 * @param featurestub
	 * @return
	 */
	private static boolean proofAlreadyExists(ProofHandler a, File evalPath, File featurestub){
		File savedProofsPath = new File(evalPath+FILE_SEPERATOR+FileManager.savedProofsDir+FILE_SEPERATOR+featurestub.getName());
		File[] proofs = savedProofsPath.listFiles();
		String defaultName= a.getTypeName()+"__"+a.getTargetName().replace(" ", "");
		if(proofs!=null){
			for(File f : proofs){
				if(!f.isDirectory()){
					if(f.getName().endsWith(".proof") && f.getName().contains(defaultName)){
						return true;
					}
				}
			}
		}
		return false;
	}
	/**
	 * 
	 * @param a
	 * @param toEvaluate
	 * @return
	 */
	private static File getOldFeatureStubProof(ProofHandler a, File toEvaluate){
		File savedProofsPath = new File(toEvaluate+FILE_SEPERATOR+FileManager.partialProofsDir);
		File[] proofs = savedProofsPath.listFiles();
		String defaultName= a.getTypeName()+"__"+a.getTargetName().replace(" ", "");
		if(proofs!=null){
			for(File f : proofs){
				if(!f.isDirectory()){
					if(f.getName().endsWith(".proof") && f.getName().contains(defaultName)){
						return f;
					}
				}
			}
		}
		return null;
	}
}
