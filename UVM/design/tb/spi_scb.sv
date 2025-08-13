class spi_scb extends uvm_scoreboard;
  `uvm_component_utils(spi_scb)

  // Use implementation port to receive transactions
  uvm_analysis_imp #(spi_tran, spi_scb) scb_imp0;
  uvm_analysis_imp #(spi_tran, spi_scb) scb_imp1;

  // Data structure to hold item across monitor reports
  spi_tran ENTIRE_tran; 
  spi_tran BIT_tran;
  // Control array
  int encountered_ENTIRE[$];
  int encountered_BIT[$];
  // file ops
  int log_fd; 

  function new(string name, uvm_component parent);
    super.new(name, parent);
    scb_imp0 = new ("scb_imp0", this);
    scb_imp1 = new ("scb_imp1", this);
    ENTIRE_tran = spi_tran::type_id::create("entire");
    BIT_tran = spi_tran::type_id::create("bit");
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    log_fd   = $fopen("scoreboard_log_entire.txt", "w");
    if (!log_fd) `uvm_fatal("SCB", "Cannot open scoreboard_log.txt");
    $fdisplay(log_fd, "Scoreboard for ENTIRE transaction, generated: %p", $time);
    $fclose(log_fd); 
    log_fd   = $fopen("scoreboard_log_bit.txt", "w");
    if (!log_fd) `uvm_fatal("SCB", "Cannot open scoreboard_log.txt");
    $fdisplay(log_fd, "Scoreboard for BIT transaction, generated: %p", $time);
    $fclose(log_fd); 
  endfunction

  function void write(spi_tran tr);
    // will need to handle based on mt and tran_id
    if (tr.mt == ENTIRE) begin 
      int idx[$] = encountered_ENTIRE.find_index() with (item == tr.tran_id); 
      if (!idx.size()) begin  // first time encounter
        encountered_ENTIRE.push_back(tr.tran_id);
        ENTIRE_tran.tran_time_start = tr.tran_time_start;
        ENTIRE_tran.mt = tr.mt;
        ENTIRE_tran.tx_data = tr.tx_data;
        ENTIRE_tran.tran_id = tr.tran_id; 
        ENTIRE_tran.tran_time_end = 0;
        ENTIRE_tran.rx_data = 8'b0;
        // print_entire(ENTIRE_tran);
      end else if  (idx.size() > 0) begin // not first time
        ENTIRE_tran.tran_time_end = tr.tran_time_end;
        ENTIRE_tran.rx_data = tr.rx_data;
        encountered_ENTIRE.delete(idx[0]);
        print_entire(ENTIRE_tran);
      end
    end 
    else if (tr.mt == BIT_MOSI) begin 
        BIT_tran.mt = tr.mt;
        BIT_tran.tran_id = tr.tran_id; 
        BIT_tran.tran_time_start = tr.tran_time_start;
        BIT_tran.tran_time_end = tr.tran_time_end;
        BIT_tran.MS_data = tr.MS_data;
        BIT_tran.tx_data = tr.tx_data;
        BIT_tran.tx_data_t024 = tr.tx_data_t024;
        print_bit(BIT_tran, 0);
    end 
    else if (tr.mt == BIT_MISO) begin
        BIT_tran.mt = tr.mt;
        BIT_tran.tran_id = tr.tran_id; 
        BIT_tran.tran_time_start = tr.tran_time_start;
        BIT_tran.tran_time_end = tr.tran_time_end;
        BIT_tran.MS_data = tr.MS_data;
        print_bit(BIT_tran, 1);
    end
    else begin 
      `uvm_warning("SCB", "Invalid transaction type from monitor detected, discarding.");
    end 
  endfunction

  // T015: Check entire transaction correctness by reporting uvm_error 
  function void print_entire(spi_tran t);
    string hdr, line;
    log_fd   = $fopen("scoreboard_log_entire.txt", "a");
    if (!log_fd) `uvm_fatal("SCB", "Cannot open scoreboard_log.txt");
    // T015: Check TX and RX value match
    if (t.tx_data === t.rx_data) begin 
      `uvm_info("SCB", $sformatf("T015 satisfied"), UVM_LOW);
    end else begin 
      `uvm_error("SCB", $sformatf("T015 violated"));
    end
    $sformat(hdr,  "%-12s %-12s %-8s %-8s %-8s",
                    "start time", "end time", "ID", "TX", "RX");
    $sformat(line, "%-12.2f %-12.2f %-8d 0x%02h    0x%02h",
                    t.tran_time_start, t.tran_time_end, t.tran_id, t.tx_data, t.rx_data);
    `uvm_info("SCB", hdr, UVM_NONE);
    `uvm_info("SCB", line, UVM_NONE);
    $fdisplay(log_fd, hdr);
    $fdisplay(log_fd, line);        
    $fclose(log_fd); 
  endfunction

  // T024: Check MOSI/MISO correctness by reporting uvm_error
  function void print_bit(spi_tran t, int mosimiso = 0);
    string hdr, line;
    log_fd   = $fopen("scoreboard_log_bit.txt", "a");
    if (!log_fd) `uvm_fatal("SCB", "Cannot open scoreboard_log.txt");
    // T001: Check mosi/miso value match
    if ((mosimiso == 0) && (t.tx_data === t.MS_data)) begin 
      `uvm_info("SCB", $sformatf("T001 satisfied"), UVM_LOW);
    end else if (mosimiso == 0) begin 
      `uvm_error("SCB", $sformatf("T001 violated, %h %h",t.tx_data, t.MS_data));
    end
    // T024: Check mosi/miso value match
    if ((mosimiso == 0) && (t.tx_data_t024 === t.MS_data)) begin 
      `uvm_info("SCB", $sformatf("T024 satisfied"), UVM_LOW);
    end else if (mosimiso == 0) begin 
      `uvm_error("SCB", $sformatf("T024 violated, %h %h",t.tx_data_t024, t.MS_data));
    end
    $sformat(hdr,  "%-12s %-12s %-8s %-8s",
                    "start time", "end time", "ID", (mosimiso) ? "miso" : "mosi");
    $sformat(line, "%-12.2f %-12.2f %-8d 0x%02h",
                    t.tran_time_start, t.tran_time_end, t.tran_id, t.MS_data);
    `uvm_info("SCB", hdr, UVM_NONE);
    `uvm_info("SCB", line, UVM_NONE);
    $fdisplay(log_fd, hdr);
    $fdisplay(log_fd, line);
    $fclose(log_fd);
  endfunction

  function void report_phase (uvm_phase phase);

  endfunction
endclass

