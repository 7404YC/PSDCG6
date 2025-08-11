class spi_cov extends uvm_component;
  `uvm_component_utils(spi_cov)
    
  // Use implementation port to receive transactions
	uvm_analysis_imp #(spi_tran, spi_cov) cov_imp;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    cov_imp = new("cov_imp", this);
    spi_cg = new();
    spi_cg.set_inst_name($sformatf("%s\ (spi_cg\)", get_full_name()));
  endfunction

  // This will be called when transactions arrive
  function void write(spi_tran tr);
    spi_cg.sample(tr);
  endfunction

  covergroup spi_cg with function sample(spi_tran tr);
	// TODO: Fill in the necessary coverpoint
  endgroup

  function void report_phase(uvm_phase phase);
    `uvm_info("COVERAGE spi_cg", $sformatf("Coverage spi_cg      : %.2f%%", spi_cg_inst.get_coverage()), UVM_NONE)
	// TODO: Complete the message display info
    //`uvm_info("COVERAGE spi_cg", $sformatf("Coverage addr_cp     : %.2f%%", spi_cg_inst.addr_cp.get_coverage()), UVM_NONE)
  endfunction
endclass
