export NR=1
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
	mkdir -p builddir_sanity_test; \
	make run_dv; \
	sed -i '$$ s/$$/ +SANITY_TEST/'  qrun; \
	cp qrun builddir_sanity_test; \
        cd builddir_sanity_test && qrun

sanity_test_reset:
	mkdir -p builddir_sanity_test_reset; \
	make run_dv; \
	sed -i '$$ s/$$/ +RST_RANDOM_EN +SANITY_TEST/' qrun; \
	cp qrun builddir_sanity_test_reset; \
	cd builddir_sanity_test_reset && qrun
	
b2b_test:
	mkdir -p builddir_b2b_reset; \
	make run_dv; \
	sed -i '$$ s/$$/ +B2B_TEST/' qrun; \
	cp qrun builddir_b2b_reset; \
	cd builddir_b2b_reset && qrun
	
b2b_test_reset:
	mkdir -p builddir_b2b_test_reset; \
	make run_dv; \
	sed -i '$$ s/$$/ +RST_RANDOM_EN +B2B_TEST/' qrun; \
	cp qrun builddir_b2b_test_reset; \
	cd builddir_b2b_test_reset && qrun

sanity_test_reset_during_trans:
	mkdir -p builddir_sanity_test_reset_during_trans; \
	make run_dv; \
	sed -i '$$ s/$$/ +SANITY_TEST_RESET_DURING_TRANS/' qrun; \
	cp qrun builddir_sanity_test_reset_during_trans; \
	cd builddir_sanity_test_reset_during_trans && qrun

b2b_test_reset_during_trans:
	mkdir -p builddir_b2b_test_reset_during_trans; \
	make run_dv; \
	sed -i '$$ s/$$/ +B2B_TEST_RESET_DURING_TRANS/' qrun; \
	cp qrun builddir_b2b_test_reset_during_trans; \
	cd builddir_b2b_test_reset_during_trans && qrun

cov:
	verdi -cov -covdir spi_simv.vdb

merge:
	urg -full64 -metric line+tgl+cond+fsm+assert+branch+group -warn none -dbname merge_coverage_name.vdb -dir ./builddir_*/spi_simv.vdb/

cov_merged:
	verdi -cov -covdir merge_coverage_name.vdb

all:
	make clean; \
	make sanity_test; \
	make sanity_test_reset; \
	make b2b_test; \
	make b2b_test_reset; \
	make sanity_test_reset_during_trans; \
	make b2b_test_reset_during_trans; \
	make merge

