class spi_cov extends uvm_component;
  `uvm_component_utils(spi_cov)
    
  // Use implementation port to receive transactions
  uvm_analysis_imp #(spi_tran, spi_cov) cov_imp;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    cov_imp = new("cov_imp", this);
    spi_cg = new();
    spi_cg.set_inst_name($sformatf("%s (spi_cg)", get_full_name()));
  endfunction

  // This will be called when transactions arrive
  function void write(spi_tran tr);
    spi_cg.sample(tr);
  endfunction

  covergroup spi_cg with function sample(spi_tran tr);
  option.per_instance = 1;
  option.comment = "THIS IS MY SPI_CG COVERAGE";

  rst_n_cp:    coverpoint tr.rst_n;
  start_cp:    coverpoint tr.start;
  busy_cp:     coverpoint tr.busy;
  done_cp:     coverpoint tr.done;
  cs_n_cp:     coverpoint tr.cs_n;
  tx_data_cp:  coverpoint tr.tx_data;
  rx_data_cp:  coverpoint tr.rx_data;
  miso_cp:     coverpoint tr.miso;
  mosi_cp:     coverpoint tr.mosi;
  init_cp: cross rst_n_cp,start_cp,busy_cp,done_cp,cs_n_cp;
  data_cp: cross tx_data_cp, rx_data_cp;
  ms_cp:   cross miso_cp, mosi_cp;

  endgroup

  function void report_phase(uvm_phase phase);
    `uvm_info("COVERAGE", $sformatf("Coverage spi_cg       : %.2f%%", spi_cg.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage rst_n_cp       : %.2f%%", spi_cg.rst_n_cp.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage start_cp       : %.2f%%", spi_cg.start_cp.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage busy_cp        : %.2f%%", spi_cg.busy_cp.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage done_cp        : %.2f%%", spi_cg.done_cp.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage cs_n_cp        : %.2f%%", spi_cg.cs_n_cp.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage tx_data_cp      : %.2f%%", spi_cg.tx_data_cp.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage rx_data_cp      : %.2f%%", spi_cg.rx_data_cp.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage miso_cp        : %.2f%%", spi_cg.miso_cp.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage mosi_cp        : %.2f%%", spi_cg.mosi_cp.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage init_cp      : %.2f%%", spi_cg.init_cp.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage data_cp      : %.2f%%", spi_cg.data_cp.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage ms_cp        : %.2f%%", spi_cg.ms_cp.get_coverage()), UVM_NONE)
  endfunction
endclass
