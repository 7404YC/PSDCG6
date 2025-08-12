class spi_scb extends uvm_scoreboard;
  `uvm_component_utils(spi_scb)

  // Use implementation port to receive transactions
  uvm_analysis_imp #(spi_tran, spi_scb) scb_imp0;
  uvm_analysis_imp #(spi_tran, spi_scb) scb_imp1;

  function new(string name, uvm_component parent);
    super.new(name, parent);
	scb_imp0 = new ("scb_imp0", this);
	scb_imp1 = new ("scb_imp1", this);
  endfunction

  function void write(spi_tran tr);

  endfunction

endclass

