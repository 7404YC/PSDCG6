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
    log_fd   = $fopen("scoreboard_log.txt", "w");
    if (!log_fd) `uvm_fatal("SCB", "Cannot open scoreboard_log.txt");
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
      end else if  (idx.size() > 0) begin // not first time
        ENTIRE_tran.tran_time_end = tr.tran_time_end;
        ENTIRE_tran.rx_data = tr.rx_data;
        encountered_ENTIRE.delete(idx[0]);
        print_entire(ENTIRE_tran);
      end
    end 
    else if (tr.mt == BIT) begin 
      int idx[$] = encountered_BIT.find_index() with (item == tr.tran_id);
      if (!idx.size()) begin  // first time encounter
        encountered_BIT.push_back(tr.tran_id);
        BIT_tran.tran_time_start = tr.tran_time_start;
        BIT_tran.mt = tr.mt;
        BIT_tran.tran_id = tr.tran_id; 
        print_bit(BIT_tran, 0);
      end else if  (idx.size() > 0) begin // not first time
        BIT_tran.tran_time_end = tr.tran_time_end;
        BIT_tran.MS_data = tr.MS_data;
        encountered_BIT.delete(idx[0]);
        print_bit(BIT_tran, 1);
      end
    end 
    else begin 
      `uvm_warning("SCB", "Invalid transaction type from monitor detected, discarding.");
    end 
  endfunction

  function void print_entire(spi_tran t);
    string hdr, line;
    $sformat(hdr,  "%-12s %-12s %-8s %-8s %-8s",
                    "start time", "end time", "ID", "TX", "RX");
    $sformat(line, "%-12.2f %-12.2f %-8d 0x%02h    0x%02h",
                    t.tran_time_start, t.tran_time_end, t.tran_id, t.tx_data, t.rx_data);
    `uvm_info("SCB", hdr, UVM_NONE);
    `uvm_info("SCB", line, UVM_NONE);
    $fdisplay(log_fd, hdr);
    $fdisplay(log_fd, line);  
  endfunction

  function void print_bit(spi_tran t, int mosimiso = 0);
    string hdr, line;
    $sformat(hdr,  "%-12s %-12s %-8s %-8s",
                    "start time", "end time", "ID", (mosimiso) ? "miso" : "mosi");
    $sformat(line, "%-12.2f %-12.2f %-8d 0x%02h",
                    t.tran_time_start, t.tran_time_end, t.tran_id, t.MS_data);
    `uvm_info("SCB", hdr, UVM_NONE);
    `uvm_info("SCB", line, UVM_NONE);
    $fdisplay(log_fd, hdr);
    $fdisplay(log_fd, line);
  endfunction
endclass

