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

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.io.IOException;
import java.util.List;

import org.eclipse.jface.layout.TableColumnLayout;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.ColumnWeightData;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TableViewerColumn;
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

import de.ovgu.featureide.core.featurehouse.proofautomation.key.AutomatingProject;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.startNewJVM;
import de.ovgu.featureide.core.featurehouse.proofautomation.model.CompleteEvaluation;
import de.ovgu.featureide.core.featurehouse.proofautomation.model.EvaluationApproach;
import de.ovgu.featureide.core.featurehouse.proofautomation.model.SingleProject;

/**
 * TODO description
 * 
 * @author Stefanie
 */
public class ProofAutomationComposite extends Composite{
	
	private File evaluationDir;
	private List<EvaluationApproach> evaluationPhaseList;
	private File currentProject;
	
	private Text source;
	private Label loadLabel;
	private Button loadVerificationDir;
	private Button loadPhaseDir;
	private Button loadProjectDir;
	private Button performVerification;
	
	//Table for all Phases
	private TableViewer resultOverviewPhases;
	private TableViewerColumn namePhases;
	private TableViewerColumn nodesPhases;
	private TableViewerColumn branchesPhases;
	private TableViewerColumn automodeTimePhases;
	private TableViewerColumn ruleApplicationPhases;
	
	//Table for a single Phase Verification
	private TableViewer resultOverviewPerPhase;
	private TableViewerColumn namePhase;
	private TableViewerColumn nodesPhase;
	private TableViewerColumn branchesPhase;
	private TableViewerColumn automodeTimePhase;
	private TableViewerColumn ruleApplicationPhase;
	
	//Table for single Project
	private TableViewer resultOverviewProject;
	private TableViewerColumn type;
	private TableViewerColumn target;
	private TableViewerColumn nodes;
	private TableViewerColumn branches;
	private TableViewerColumn automodeTime;
	private TableViewerColumn ruleApplication;
	
	
	

	/**
	 * @param parent
	 * @param style
	 */
	public ProofAutomationComposite(Composite parent, int style) {
		super(parent, style);
		setLayout(new GridLayout(1,false));
		generateLoadPart();
		generateEvaluationPart(style);
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
		Composite buttonComposite = new Composite(load, SWT.NONE);
		buttonComposite.setLayout(new GridLayout(3,true));
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
				File f = new File(source.getText());
				CompleteEvaluation ce = new CompleteEvaluation(f);
				ce.performEvaluation();
			}
		} );
		loadProjectDir.addSelectionListener( new SelectionListener() {
			@Override
			public void widgetDefaultSelected(SelectionEvent e) {
				// TODO Auto-generated method stub
				
			}
			@Override
			public void widgetSelected(SelectionEvent e) {
				File f = new File(source.getText());
				SingleProject s = new SingleProject(f,0);
				startNewJVM.startNewProcess(s.toEvaluate,s.evaluatePath);
				//s.performEvaluation();
			}
		} );
		loadPhaseDir.addSelectionListener( new SelectionListener() {
			@Override
			public void widgetDefaultSelected(SelectionEvent e) {
				// TODO Auto-generated method stub
				
			}
			@Override
			public void widgetSelected(SelectionEvent e) {
				File f = new File(source.getText());
				EvaluationApproach ep = new EvaluationApproach(f);
				ep.performEvaluation();
			}
		} );
		
		return load;
	}

	private Group generateEvaluationPart(int style){
		Group tables = new Group(this,1);
		tables.setText("Evaluation");
		tables.setLayout(new GridLayout(1,false));
		tables.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		tableCreator(tables,style);
		
		return tables;
	}
	
	private void tableCreator(Composite parent, int style){
/*		Composite tableComposite = new Composite(parent, SWT.NONE);
        tableComposite.setLayoutData(new GridData(GridData.FILL_BOTH));
        TableColumnLayout tableLayout = new TableColumnLayout();
        tableComposite.setLayout(tableLayout);
		resultOverviewPhases = new TableViewer(tableComposite, SWT.MULTI | SWT.FULL_SELECTION);
		namePhases = new TableViewerColumn(resultOverviewPhases, style);
		nodesPhases = new TableViewerColumn(resultOverviewPhases, style);
		branchesPhases = new TableViewerColumn(resultOverviewPhases, style);
		automodeTimePhases = new TableViewerColumn(resultOverviewPhases, style);
		ruleApplicationPhases = new TableViewerColumn(resultOverviewPhases, style);
		namePhases.getColumn().setText("Name");
		namePhases.getColumn().setMoveable(true);
		tableLayout.setColumnData(namePhases.getColumn(), new ColumnWeightData(15));
		nodesPhases.getColumn().setText("Nodes");
		nodesPhases.getColumn().setMoveable(true);
		tableLayout.setColumnData(nodesPhases.getColumn(), new ColumnWeightData(15));
		branchesPhases.getColumn().setText("Branches");
		branchesPhases.getColumn().setMoveable(true);
		tableLayout.setColumnData(branchesPhases.getColumn(), new ColumnWeightData(15));
		automodeTimePhases.getColumn().setText("Automode Time");
		automodeTimePhases.getColumn().setMoveable(true);
		tableLayout.setColumnData(automodeTimePhases.getColumn(), new ColumnWeightData(15));
		ruleApplicationPhases.getColumn().setText("Rule Applications");
		ruleApplicationPhases.getColumn().setMoveable(true);
		tableLayout.setColumnData(ruleApplicationPhases.getColumn(), new ColumnWeightData(15));
		
		resultOverviewPhases.setContentProvider(ArrayContentProvider.getInstance());
		
		resultOverviewPhases.addSelectionChangedListener(new ISelectionChangedListener() {
	           @Override
	           public void selectionChanged(SelectionChangedEvent event) {
	              
	           }
	        });
		resultOverviewPhases.getTable().setHeaderVisible(true);
		resultOverviewPhases.getTable().setLinesVisible(true);*/
		
	}
}
