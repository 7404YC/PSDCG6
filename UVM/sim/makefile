export NR ?= 1
export GEN_QRUN ?= 1

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
	\rm -frd *.vdb builddir* 

run_dv:
	@if [ ! -f qrun ]; then \
		${ROOT}/sim/run_sim.csh dv ${MODULE}; \
	fi

sanity_test: 
	mkdir -p builddir/$@
ifeq ($(GEN_QRUN), 1)
	make run_dv
endif
	cp qrun builddir/$@
	sed -i '$$ s/$$/ +SANITY_TEST/' builddir/$@/qrun
	cd builddir/$@ && qrun

sanity_test_reset:
	mkdir -p builddir/$@
ifeq ($(GEN_QRUN), 1)
	make run_dv
endif
	cp qrun builddir/$@
	sed -i '$$ s/$$/ +RST_RANDOM_EN +SANITY_TEST/' builddir/$@/qrun
	cd builddir/$@ && qrun
	
b2b_test:
	mkdir -p builddir/$@
ifeq ($(GEN_QRUN), 1)
	make run_dv
endif
	cp qrun builddir/$@
	sed -i '$$ s/$$/ +B2B_TEST/' builddir/$@/qrun
	cd builddir/$@ && qrun
	
b2b_test_reset:
	mkdir -p builddir/$@
ifeq ($(GEN_QRUN), 1)
	make run_dv
endif
	cp qrun builddir/$@
	sed -i '$$ s/$$/ +RST_RANDOM_EN +B2B_TEST/' builddir/$@/qrun
	cd builddir/$@ && qrun

sanity_test_reset_during_trans:
	mkdir -p builddir/$@
ifeq ($(GEN_QRUN), 1)
	make run_dv
endif
	cp qrun builddir/$@
	sed -i '$$ s/$$/ +SANITY_TEST_RESET_DURING_TRANS/' builddir/$@/qrun
	cd builddir/$@ && qrun

b2b_test_reset_during_trans:
	mkdir -p builddir/$@
ifeq ($(GEN_QRUN), 1)
	make run_dv
endif
	cp qrun builddir/$@
	sed -i '$$ s/$$/ +B2B_TEST_RESET_DURING_TRANS/' builddir/$@/qrun
	cd builddir/$@ && qrun

cov:
	verdi -cov -covdir spi_simv.vdb

merge:
	urg -full64 -metric line+tgl+cond+fsm+assert+branch+group -warn none -dbname merge_coverage_name.vdb -dir ./builddir/*/spi_simv.vdb/

cov_merged:
	verdi -cov -covdir merge_coverage_name.vdb

all:
	make clean
	make dv
	export GEN_QRUN=0; \
	make -j \
		sanity_test \
		sanity_test_reset \
		sanity_test_reset_during_trans \
		b2b_test \
		b2b_test_reset \
		b2b_test_reset_during_trans
	make merge


