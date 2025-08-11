class spi_scb extends uvm_scoreboard;
  `uvm_component_utils(spi_scb)

  // Use implementation port to receive transactions
  uvm_analysis_imp #(spi_tran, spi_scb) scb_imp;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction


endclass

