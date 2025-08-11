class spi_test extends uvm_test;
  `uvm_component_utils(spi_test)

  spi_env env;
  spi_seq seq;

  int seq_count = 20;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = spi_env::type_id::create("env", this);
  endfunction

  task run_phase(uvm_phase phase);
    seq = spi_seq::type_id::create("seq");

    seq.seq_count = this.seq_count;

    `uvm_info("TEST", $sformatf("Starting sequences with config:\n\
                                Normal: count=%0d\n\
                                High: count=%0d\n\
                                Low: count=%0d",
                                seq.seq_count,
                                hseq.seq_count,
                                lseq.seq_count),
                                UVM_MEDIUM)

    phase.raise_objection(this);
    fork
      seq.start(env.agt.sqr);
    join
    //wait((env.con.wr_num_processed + env.con.wr_fifo_overflows == env.con.wr_num_received) && (env.con.rd_num_processed + env.con.rd_fifo_overflows == env.con.rd_num_received));
    phase.drop_objection(this);
  endtask
endclass