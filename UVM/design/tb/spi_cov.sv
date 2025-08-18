class spi_cov extends uvm_component;
  `uvm_component_utils(spi_cov)
    
  // Use implementation port to receive transactions
  uvm_analysis_imp #(spi_tran, spi_cov) cov_imp;

  // Virtual interface
  virtual spi_if vif;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    cov_imp = new("cov_imp", this);
    spi_cg = new();
    spi_cg.set_inst_name($sformatf("%s (spi_cg)", get_full_name()));
  endfunction

  // This will be called when transactions arrive
  function void write(spi_tran tr);
  //  spi_cg.sample(tr);
  endfunction

  function void build_phase(uvm_phase phase);
    if (!uvm_config_db#(virtual spi_if)::get(this, "", "vif", vif)) begin
      `uvm_error("COV", "vif not found in config db")
    end
  endfunction

  task run_phase(uvm_phase phase);
	forever begin
        	@(vif.clk);
		spi_cg.sample();
	end	
  endtask

  covergroup spi_cg;
  option.per_instance = 1;
  option.comment = "THIS IS MY SPI_CG COVERAGE";

  rst_n_cp:    coverpoint vif.rst_n;
  start_cp:    coverpoint vif.start;
  busy_cp:     coverpoint vif.busy;
  done_cp:     coverpoint vif.done;
  cs_n_cp:     coverpoint vif.cs_n;
  tx_data_cp:  coverpoint vif.tx_data;
  rx_data_cp:  coverpoint vif.rx_data { bins specific_value = {8'hB9}; }
  miso_cp:     coverpoint vif.miso;
  mosi_cp:     coverpoint vif.mosi;
  input_cp:   cross  tx_data_cp,rst_n_cp,start_cp;

  endgroup

  function void report_phase(uvm_phase phase);
    `uvm_info("COVERAGE", $sformatf("Coverage spi_cg      : %.2f%%", spi_cg.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage rst_n_cp    : %.2f%%", spi_cg.rst_n_cp.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage start_cp    : %.2f%%", spi_cg.start_cp.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage busy_cp     : %.2f%%", spi_cg.busy_cp.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage done_cp     : %.2f%%", spi_cg.done_cp.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage cs_n_cp     : %.2f%%", spi_cg.cs_n_cp.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage tx_data_cp  : %.2f%%", spi_cg.tx_data_cp.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage rx_data_cp  : %.2f%%", spi_cg.rx_data_cp.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage miso_cp     : %.2f%%", spi_cg.miso_cp.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage mosi_cp     : %.2f%%", spi_cg.mosi_cp.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage input_cp    : %.2f%%", spi_cg.input_cp.get_coverage()), UVM_NONE)
  endfunction
endclass
