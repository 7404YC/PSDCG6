class spi_seq extends uvm_sequence #(spi_tran);
  `uvm_object_utils(spi_seq)

  function new(string name = "spi_seq");
    super.new(name);
  endfunction

  task body();
  endtask
endclass

