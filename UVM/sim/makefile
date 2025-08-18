export NR ?= 1
export GEN_QRUN ?= 1
export TEST_SEED ?= 0

ifeq ($(TEST_SEED), 0)
	export SEED := $(shell echo $$RANDOM)
else
	export SEED := $(TEST_SEED)
endif

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
	\rm -frd *.vdb builddir* summary.log 

run_dv:
	@if [ ! -f qrun ]; then \
		${ROOT}/sim/run_sim.csh dv ${MODULE}; \
	fi

sanity_test: 
	mkdir -p builddir/$@/$(SEED)
ifeq ($(GEN_QRUN), 1)
	make run_dv
endif
	cp qrun builddir/$@/$(SEED)
	sed -i '$$ s/$$/ +ntb_random_seed=${SEED} +SANITY_TEST/' builddir/$@/$(SEED)/qrun
	cd builddir/$@/$(SEED) && qrun

sanity_reset_test:
	mkdir -p builddir/$@/$(SEED)
ifeq ($(GEN_QRUN), 1)
	make run_dv
endif
	cp qrun builddir/$@/$(SEED)
	sed -i '$$ s/$$/ +ntb_random_seed=${SEED} +RST_RANDOM_EN +SANITY_TEST/' builddir/$@/$(SEED)/qrun
	cd builddir/$@/$(SEED) && qrun
	
b2b_test:
	mkdir -p builddir/$@/$(SEED)
ifeq ($(GEN_QRUN), 1)
	make run_dv
endif
	cp qrun builddir/$@/$(SEED)
	sed -i '$$ s/$$/ +ntb_random_seed=${SEED} +B2B_TEST/' builddir/$@/$(SEED)/qrun
	cd builddir/$@/$(SEED) && qrun
	
b2b_reset_test:
	mkdir -p builddir/$@/$(SEED)
ifeq ($(GEN_QRUN), 1)
	make run_dv
endif
	cp qrun builddir/$@/$(SEED)
	sed -i '$$ s/$$/ +ntb_random_seed=${SEED} +RST_RANDOM_EN +B2B_TEST/' builddir/$@/$(SEED)/qrun
	cd builddir/$@/$(SEED) && qrun

sanity_reset_during_trans_test:
	mkdir -p builddir/$@/$(SEED)
ifeq ($(GEN_QRUN), 1)
	make run_dv
endif
	cp qrun builddir/$@/$(SEED)
	sed -i '$$ s/$$/ +ntb_random_seed=${SEED} +SANITY_RESET_DURING_TRANS_TEST/' builddir/$@/$(SEED)/qrun
	cd builddir/$@/$(SEED) && qrun

b2b_reset_during_trans_test:
	mkdir -p builddir/$@/$(SEED)
ifeq ($(GEN_QRUN), 1)
	make run_dv
endif
	cp qrun builddir/$@/$(SEED)
	sed -i '$$ s/$$/ +ntb_random_seed=${SEED} +B2B_RESET_DURING_TRANS_TEST/' builddir/$@/$(SEED)/qrun
	cd builddir/$@/$(SEED) && qrun

cov:
	verdi -cov -covdir spi_simv.vdb

merge:
	urg -full64 -metric line+tgl+cond+fsm+assert+branch+group -warn none -dbname merge_coverage_name.vdb -dir ./builddir*/*/*/spi_simv.vdb/

cov_merged:
	verdi -cov -covdir merge_coverage_name.vdb

all:
	make run_dv
	export GEN_QRUN=0; \
	make -j \
		sanity_test \
		sanity_reset_test \
		sanity_reset_during_trans_test \
		b2b_test \
		b2b_reset_test \
		b2b_reset_during_trans_test
	make merge

result:
	rm -rf summary.log
	@for f in builddir/*/*/spi_sim.log; do \
	  echo "=== $$f ===" >> summary.log; \
	  awk '/--- UVM Report Summary ---/ {flag=1} flag' $$f >> summary.log; \
	  echo "" >> summary.log; \
	done
