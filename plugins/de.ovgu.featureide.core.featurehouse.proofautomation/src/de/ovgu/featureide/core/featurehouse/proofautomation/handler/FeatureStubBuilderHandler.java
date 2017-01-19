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
package de.ovgu.featureide.core.featurehouse.proofautomation.handler;

import java.io.File;
import java.io.IOException;

import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.featurehouse.proofautomation.builder.BuilderUtil;
import de.ovgu.featureide.core.featurehouse.proofautomation.builder.FeatureStubBuilder;
import de.ovgu.featureide.core.featurehouse.proofautomation.builder.MetaProductBuilder;
import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.AutomatingProject;
import de.ovgu.featureide.featurehouse.FeatureHouseComposer;
import de.ovgu.featureide.featurehouse.FeatureHouseCorePlugin;
import de.ovgu.featureide.featurehouse.meta.FeatureStubsGenerator;
import de.ovgu.featureide.featurehouse.ui.handlers.BuildMetaProductHandler;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.ui.handlers.base.AFeatureProjectHandler;

public class FeatureStubBuilderHandler extends AFeatureProjectHandler{
	public static String FILE_SEPERATOR = System.getProperty("file.separator");
	@Override
	protected void singleAction(IFeatureProject featureProject) {
//		FeatureStubsGenerator fsg = new FeatureStubsGenerator(featureProject);
//		fsg.generate();
//		buildMetaproduct(featureProject);
		featureProject.buildRelevantChanges();
		File transactionAccount = new File(getAbsoluteProjectPath(featureProject)+FILE_SEPERATOR+"Transaction"+FILE_SEPERATOR+"Account.java");
		File lockAccount = new File(getAbsoluteProjectPath(featureProject)+FILE_SEPERATOR+"Lock"+FILE_SEPERATOR+"Account.java");
		File metap = new File(getProjectPath(featureProject)+FILE_SEPERATOR+"src"+FILE_SEPERATOR+"Account.java");
		FeatureStubBuilder.prepareForVerification(transactionAccount,lockAccount);
		BuilderUtil.removeBracketsOfVar(metap, "lock");
		AutomatingProject a = new AutomatingProject();
		a.performFeaturestubVerification(new File(getProjectPath(featureProject)));
		FileManager.copySavedProofsToPartialProofs(new File(getProjectPath(featureProject)));
		MetaProductBuilder.preparePartialProofs(new File(getProjectPath(featureProject)));
		a.performMetaproductVerification(new File(getProjectPath(featureProject)));
		try {
			a.getBufferedWriter().close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public String getAbsoluteProjectPath(IFeatureProject featureProject){
		return getProjectPath(featureProject)+FILE_SEPERATOR+featureProject.getFeaturestubPath();
	}
	
	public String getProjectPath(IFeatureProject featureProject){
		String projectPath = featureProject.getProject().getRawLocation().toString();
		projectPath.replace("/", FILE_SEPERATOR);
		return projectPath;
	}
	
	protected void buildMetaproduct(IFeatureProject featureProject){
		if (FeatureHouseComposer.COMPOSER_ID.equals(featureProject.getComposerID())) {
			final FeatureHouseComposer featureHouseComposer = (FeatureHouseComposer) featureProject.getComposer();
			featureHouseComposer.setBuildMetaProduct(!featureHouseComposer.buildMetaProduct());
			
			LongRunningMethod<Boolean> job = new LongRunningMethod<Boolean>() {
				@Override
				public Boolean execute(IMonitor workMonitor) throws Exception {
					try {
						featureProject.getProject().build(IncrementalProjectBuilder.FULL_BUILD, null);
					} catch (CoreException e) {
						FeatureHouseCorePlugin.getDefault().logError(e);
					}
					return true;
				}
			};
			LongRunningWrapper.getRunner(job, "Build meta product for project \"" + featureProject.getProjectName() + "\".").schedule();
		}
	}
}
