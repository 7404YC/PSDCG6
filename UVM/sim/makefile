dv: clean run_dv

clean:
	\rm -frd novas* mkdir csrc
	\rm -frd ${MODULE}_comp.log ${MODULE}_sim.log ${MODULE}_sim.rpt ${MODULE}_simv ${MODULE}_sim.vcd ${MODULE}_sim.fsdb ${MODULE}_simv.daidir ${MODULE}_ana.log
	\rm -frd ${MODULE}_sim.vcd.vpd
	\rm -frd ucli.key worklib debug.report
	\rm -frd DVEfiles dve_report.* opendatabase.log
	\rm -frd verdiLog inter.fsdb
	\rm -frd seed* sysBusyP* vc_hdrs.h
	\rm -frd bus_cov ${MODULE}_simv.vdb cm.log .fsm.sch.verilog.xml
	\rm -frd qrun sysProgressP.conf sysProgressPLog vdCov.conf vdCovLog

run_dv:
	${ROOT}/sim/run_sim.csh dv ${MODULE}

sanity_test: 
	export NR=1; \
	make run_dv; \
	sed -i '$$ s/$$/ +SANITY_TEST/' qrun; \
	qrun

sanity_test_reset:
	export NR=1; \
	make run_dv; \
	sed -i '$$ s/$$/ +RST_RANDOM_EN +SANITY_TEST/' qrun; \
	qrun
	
b2b_test:
	export NR=1; \
	make run_dv; \
	sed -i '$$ s/$$/ +B2B_TEST/' qrun; \
	qrun
	
b2b_test_reset:
	export NR=1; \
	make run_dv; \
	sed -i '$$ s/$$/ +RST_RANDOM_EN +B2B_TEST/' qrun; \
	qrun

sanity_test_reset_during_trans:
	export NR=1; \
	make run_dv; \
	sed -i '$$ s/$$/ +SANITY_TEST_RESET_DURING_TRANS/' qrun; \
	qrun

b2b_test_reset_during_trans:
	export NR=1; \
	make run_dv; \
	sed -i '$$ s/$$/ +B2B_TEST_RESET_DURING_TRANS/' qrun; \
	qrun
