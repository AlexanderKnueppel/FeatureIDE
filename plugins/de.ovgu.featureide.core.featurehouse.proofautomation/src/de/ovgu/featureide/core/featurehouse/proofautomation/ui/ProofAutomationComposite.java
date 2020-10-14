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
package de.ovgu.featureide.core.featurehouse.proofautomation.ui;

import java.io.File;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

import de.ovgu.featureide.core.featurehouse.proofautomation.builder.projectWorker;
import de.ovgu.featureide.core.featurehouse.proofautomation.configuration.Configuration;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.AutomatingProject;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.startNewJVM;
import de.ovgu.featureide.core.featurehouse.proofautomation.model.CompleteEvaluation;
import de.ovgu.featureide.core.featurehouse.proofautomation.model.EvaluationApproach;
import de.ovgu.featureide.core.featurehouse.proofautomation.model.SingleProject;

/**
 * Prepares the view for eclipse
 * 
 * @author Stefanie
 */
public class ProofAutomationComposite extends Composite{
	
	private Text key;
	private Label keyLabel;
	private Text keyLibs;
	private Label keyLibsLabel;
	
	private Text source;
	private Label loadLabel;
	private Text verificationApproach;
	private Label vaLabel;
	private Button loadVerificationDir;
	private Button loadPhaseDir;
	private Button loadProjectDir;
	private Button sandbox;
	
	
	

	/**
	 * @param parent
	 * @param style
	 */
	public ProofAutomationComposite(Composite parent, int style) {
		super(parent, style);
		setLayout(new GridLayout(1,false));
		generateConfigPart();
		generateLoadPart();
	}
	
	private void generateConfigPart(){
		Group config = new Group(this, 1);
		config.setText("Configuration");
		config.setLayout(new GridLayout(1,false));
		config.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		Composite configComposite = new Composite(config, SWT.NONE);
		configComposite.setLayout(new GridLayout(2,false));
		configComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		keyLabel = new Label(configComposite, SWT.NONE);
		keyLabel.setText("Key binary Path:");
		key = new Text(configComposite, SWT.BORDER);
		key.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		Composite configComposite2 = new Composite(config, SWT.NONE);
		configComposite2.setLayout(new GridLayout(2,false));
		configComposite2.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		keyLibsLabel = new Label(configComposite2, SWT.NONE);
		keyLibsLabel.setText("Key Library Path:");
		keyLibs = new Text(configComposite2, SWT.BORDER);
		keyLibs.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
	}
	
	private Group generateLoadPart(){
		Group load = new Group(this, 1);
		load.setText("Directory for Evaluation");
		load.setLayout(new GridLayout(1,false));
		load.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		Composite loadComposite = new Composite(load, SWT.NONE);
		loadComposite.setLayout(new GridLayout(2,false));
		loadComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		loadLabel = new Label(loadComposite, SWT.NONE);
		loadLabel.setText("Directory:");
		source = new Text(loadComposite, SWT.BORDER);
		source.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		source.setText("/mnt/54AFF99F466B2AED/Informatik/Masterarbeit/eval (1)");
		vaLabel = new Label(loadComposite, SWT.NONE);
		vaLabel.setText("Verification Approach:");
		verificationApproach = new Text(loadComposite, SWT.BORDER);
		verificationApproach.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		verificationApproach.setText("1");
		Composite buttonComposite = new Composite(load, SWT.NONE);
		buttonComposite.setLayout(new GridLayout(4,true));
		buttonComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		loadVerificationDir = new Button (buttonComposite, SWT.PUSH);
		loadVerificationDir.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		loadPhaseDir = new Button (buttonComposite, SWT.PUSH);
		loadPhaseDir.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		loadProjectDir = new Button (buttonComposite, SWT.PUSH);
		loadProjectDir.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		loadVerificationDir.setText("Start Evaluation");
		loadPhaseDir.setText("Start Evaluation of a single Phase");
		loadProjectDir.setText("Start Project Evaluation");
		loadVerificationDir.addSelectionListener( new SelectionListener() {
			@Override
			public void widgetDefaultSelected(SelectionEvent e) {
				
			}
			@Override
			public void widgetSelected(SelectionEvent e) {
				setKey();
				File f = new File(source.getText());
				CompleteEvaluation ce = new CompleteEvaluation(f);
				if(Configuration.performVerification){
					ce.performEvaluation();
				}
			}
		} );
		loadProjectDir.addSelectionListener( new SelectionListener() {
			@Override
			public void widgetDefaultSelected(SelectionEvent e) {
				// TODO Auto-generated method stub
				
			}
			@Override
			public void widgetSelected(SelectionEvent e) {
				setKey();
				File f = new File(source.getText());
				SingleProject s = new SingleProject(f,verificationApproach.getText());
				if(Configuration.performVerification){
					startNewJVM.startNewProcess(s.toEvaluate,s.evaluatePath);
					
				}
			}
		} );
		loadPhaseDir.addSelectionListener( new SelectionListener() {
			@Override
			public void widgetDefaultSelected(SelectionEvent e) {
				// TODO Auto-generated method stub
				
			}
			@Override
			public void widgetSelected(SelectionEvent e) {
				setKey();
				File f = new File(source.getText());
				EvaluationApproach ep = new EvaluationApproach(f, verificationApproach.getText());
				if(Configuration.performVerification){
					ep.performEvaluation();
				}
			}
		} );
		
		sandbox = new Button (buttonComposite, SWT.PUSH);
		sandbox.setText("Sandbox");
		sandbox.addSelectionListener( new SelectionListener() {
			@Override
			public void widgetDefaultSelected(SelectionEvent e) {
				// TODO Auto-generated method stub
				
			}
			@Override
			public void widgetSelected(SelectionEvent e) {
				//projectWorker.sandbox();
				AutomatingProject.sandboxV2();
			}
		} );
		
		return load;
	}
	
	private void setKey(){
		if(!key.getText().isEmpty()){
			Configuration.keyBinPath = key.getText();
		}
		if(!keyLibs.getText().isEmpty()){
			Configuration.keyLibsPath = keyLibs.getText();
		}
	}
}
