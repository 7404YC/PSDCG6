class spi_scb extends uvm_scoreboard;
  `uvm_component_utils(spi_scb)

  // Use implementation port to receive transactions
  uvm_analysis_imp #(spi_tran, spi_scb) scb_imp0;
  uvm_analysis_imp #(spi_tran, spi_scb) scb_imp1;

  // Data structure to hold item across monitor reports
  spi_tran ENTIRE_tran; 
  spi_tran BIT_tran;
  spi_tran OL0HA0_if;
  spi_tran OL0HA1_L_if;
  spi_tran OL0HA1_T_if;
  spi_tran OL1HA0_if;
  spi_tran OL1HA1_L_if;
  spi_tran OL1HA1_T_if;
  // Control array
  int encountered_ENTIRE[$];
  int encountered_BIT[$];
  // file ops
  int log_fd; 
  // Check array - checkeray
  bit checkeray[$][8];
  task ensure_index(int id);
    // Grow the queue if needed 
    while (checkeray.size() <= id)
      checkeray.push_back('{default:0});
  endtask
function void check_checkeray();
    int idx_list_a[] = '{2,4,6};
    int idx_list_b[] = '{3,5,7};
    bit mismatch_046 [2:0];  // indexes: {col0, col4, col6}
    bit mismatch_157  [2:0];  // indexes: {col1, col5, col7}

    // =====================
    // Check for mismatches
    // =====================
    foreach (checkeray[row_id]) begin
        bit ref0 = checkeray[row_id][0]; // value for indices 2,4,6
        bit ref1 = checkeray[row_id][1]; // value for indices 3,5,7

        // Check group A
        foreach (idx_list_a[ii]) begin
            if (checkeray[row_id][idx_list_a[ii]] !== ref0)
                $error("Row %0d, index %0d: expected %b (from idx 0), got %b",
                       row_id, idx_list_a[ii], ref0, checkeray[row_id][idx_list_a[ii]]);
        end

        // Check group B
        foreach (idx_list_b[ii]) begin
            if (checkeray[row_id][idx_list_b[ii]] !== ref1)
                $error("Row %0d, index %0d: expected %b (from idx 1), got %b",
                       row_id, idx_list_b[ii], ref1, checkeray[row_id][idx_list_b[ii]]);
        end
    end

    // =====================
    // Dump full array
    // =====================
    $display("\n================ CHECKER ARRAY DUMP ================");
    $display(" Row | b0 b1 b2 b3 b4 b5 b6 b7 ");
    $display("-----+-------------------------");
    foreach (checkeray[row_id]) begin
        $write(" %3d |", row_id);
        for (int col = 0; col < 8; col++) begin
            $write(" %b ", checkeray[row_id][col]);
        end
        $display(""); // newline
    end
    $display("=====================================================\n");

    // Track mismatch flags

    // Iterate rows
    foreach (checkeray[row_id]) begin
        // Check group A (0,4,6 vs 2)
        if (checkeray[row_id][0] !== checkeray[row_id][2]) mismatch_046[0] = 1;
        if (checkeray[row_id][4] !== checkeray[row_id][2]) mismatch_046[1] = 1;
        if (checkeray[row_id][6] !== checkeray[row_id][2]) mismatch_046[2] = 1;

        if (mismatch_046[0] && mismatch_046[1] && mismatch_046[2]) begin
            $error("Cols (0,4,6) all had mismatches vs col 2 by row %0d", row_id);
            break;
        end

        // Check group B (1,5,7 vs 3)
        if (checkeray[row_id][1] !== checkeray[row_id][3]) mismatch_157[0] = 1;
        if (checkeray[row_id][5] !== checkeray[row_id][3]) mismatch_157[1] = 1;
        if (checkeray[row_id][7] !== checkeray[row_id][3]) mismatch_157[2] = 1;

        if (mismatch_157[0] && mismatch_157[1] && mismatch_157[2]) begin
            $error("Cols (1,5,7) all had mismatches vs col 3 by row %0d", row_id);
            break;
        end
    end
endfunction




  function new(string name, uvm_component parent);
    super.new(name, parent);
    scb_imp0 = new ("scb_imp0", this);
    scb_imp1 = new ("scb_imp1", this);
    ENTIRE_tran = spi_tran::type_id::create("entire");
    BIT_tran = spi_tran::type_id::create("bit");
    OL0HA0_if = spi_tran::type_id::create("OL0HA0_if");
    OL0HA1_L_if = spi_tran::type_id::create("OL0HA1_L_if");
    OL0HA1_T_if = spi_tran::type_id::create("OL0HA1_T_if");
    OL1HA0_if = spi_tran::type_id::create("OL1HA0_if");
    OL1HA1_L_if = spi_tran::type_id::create("OL1HA1_L_if");
    OL1HA1_T_if = spi_tran::type_id::create("OL1HA1_T_if");
	if (!uvm_config_db#(logic [7:0])::get(this, "", "slave_reset_resp", slave_reset_response))
      `uvm_fatal("SCB", "Unable to obtain slave reset resp");
  endfunction

  function void build_phase(uvm_phase phase); 
    super.build_phase(phase);
    log_fd   = $fopen("scoreboard_log_entire.txt", "w");
    if (!log_fd) `uvm_fatal("SCB", "Cannot open scoreboard_log.txt");
    $fdisplay(log_fd, "Scoreboard for ENTIRE transaction");
    $fclose(log_fd); 
    log_fd   = $fopen("scoreboard_log_bit.txt", "w");
    if (!log_fd) `uvm_fatal("SCB", "Cannot open scoreboard_log.txt");
    $fdisplay(log_fd, "Scoreboard for BIT transaction");
    $fclose(log_fd); 
    log_fd   = $fopen("scoreboard_log_OL0HA0.txt", "w");
    if (!log_fd) `uvm_fatal("SCB", "Cannot open scoreboard_log.txt");
    $fdisplay(log_fd, "Scoreboard for OL0HA0 transaction");
    $fclose(log_fd); 
    log_fd   = $fopen("scoreboard_log_OL0HA1_L.txt", "w");
    if (!log_fd) `uvm_fatal("SCB", "Cannot open scoreboard_log.txt");
    $fdisplay(log_fd, "Scoreboard for OL0HA1_L transaction");
    $fclose(log_fd); 
    log_fd   = $fopen("scoreboard_log_OL0HA1_T.txt", "w");
    if (!log_fd) `uvm_fatal("SCB", "Cannot open scoreboard_log.txt");
    $fdisplay(log_fd, "Scoreboard for OL0HA1_T transaction");
    $fclose(log_fd); 
    log_fd   = $fopen("scoreboard_log_OL1HA0.txt", "w");
    if (!log_fd) `uvm_fatal("SCB", "Cannot open scoreboard_log.txt");
    $fdisplay(log_fd, "Scoreboard for OL1HA0 transaction");
    $fclose(log_fd); 
    log_fd   = $fopen("scoreboard_log_OL1HA1_L.txt", "w");
    if (!log_fd) `uvm_fatal("SCB", "Cannot open scoreboard_log.txt");
    $fdisplay(log_fd, "Scoreboard for OL1HA1_L transaction");
    $fclose(log_fd); 
    log_fd   = $fopen("scoreboard_log_OL1HA1_T.txt", "w");
    if (!log_fd) `uvm_fatal("SCB", "Cannot open scoreboard_log.txt");
    $fdisplay(log_fd, "Scoreboard for OL1HA1_T transaction");
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
    else if (tr.mt == OL0HA0) begin 
      OL0HA0_if.mt = tr.mt;
      OL0HA0_if.tran_time_start = tr.tran_time_start;
      OL0HA0_if.mosi = tr.mosi;
      OL0HA0_if.miso = tr.miso;
      OL0HA0_if.curr_lead = tr.curr_lead;
      print_OLHA(OL0HA0_if, 0);
      ensure_index(tr.curr_lead);
      checkeray[tr.curr_lead][0] = tr.mosi;
      checkeray[tr.curr_lead][1] = tr.miso;
    end
    else if (tr.mt == OL0HA1_L) begin 
      OL0HA1_L_if.mt = tr.mt;
      OL0HA1_L_if.tran_time_start = tr.tran_time_start;
      OL0HA1_L_if.mosi = tr.mosi;
      OL0HA1_L_if.curr_lead = tr.curr_lead;
      print_OLHA(OL0HA1_L_if, 1);
      ensure_index(tr.curr_lead);
      checkeray[tr.curr_lead][2] = tr.mosi;
    end
    else if (tr.mt == OL0HA1_T) begin 
      OL0HA1_T_if.mt = tr.mt;
      OL0HA1_T_if.tran_time_start = tr.tran_time_start;
      OL0HA1_T_if.miso = tr.miso;
      OL0HA1_T_if.curr_fall = tr.curr_fall;
      print_OLHA(OL0HA1_T_if, 2);
      ensure_index(tr.curr_fall);
      checkeray[tr.curr_fall][3] = tr.miso;
    end
    else if (tr.mt == OL1HA0) begin 
      OL1HA0_if.mt = tr.mt;
      OL1HA0_if.tran_time_start = tr.tran_time_start;
      OL1HA0_if.mosi = tr.mosi;
      OL1HA0_if.miso = tr.miso;
      OL1HA0_if.curr_lead = tr.curr_lead;
      print_OLHA(OL1HA0_if, 3);
      ensure_index(tr.curr_lead);
      checkeray[tr.curr_lead][4] = tr.mosi;
      checkeray[tr.curr_lead][5] = tr.miso;
    end
    else if (tr.mt == OL1HA1_L) begin 
      OL1HA1_L_if.mt = tr.mt;
      OL1HA1_L_if.tran_time_start = tr.tran_time_start;
      OL1HA1_L_if.miso = tr.miso;
      OL1HA1_L_if.curr_lead = tr.curr_lead;
      print_OLHA(OL1HA1_L_if, 4);
      ensure_index(tr.curr_lead);
      checkeray[tr.curr_lead][7] = tr.miso;
    end
    else if (tr.mt == OL1HA1_T) begin 
      OL1HA1_T_if.mt = tr.mt;
      OL1HA1_T_if.tran_time_start = tr.tran_time_start;
      OL1HA1_T_if.mosi = tr.mosi;
      OL1HA1_T_if.curr_fall = tr.curr_fall;
      print_OLHA(OL1HA1_T_if, 5);
      ensure_index(tr.curr_fall);
      checkeray[tr.curr_fall][6] = tr.mosi;
    end
    else begin 
      `uvm_warning("SCB", "Invalid transaction type from monitor detected, discarding.");
    end 
    if (tr.mt == BIT_RESET) begin
      check_T021(tr);
    end
    if (tr.mt == ENTIRE) begin
      check_T022(tr);
    end
  endfunction

  function void print_OLHA(spi_tran t, int mode);
    string hdr, line;

    if (mode == 0) begin 
      log_fd   = $fopen("scoreboard_log_OL0HA0.txt", "a");
      if (!log_fd) `uvm_fatal("SCB", "Cannot open scoreboard_log.txt");
      $sformat(hdr,  "%-14s | %-12s | %-8s | %-8s | %-8s",
                    "type", "start time", "mosi", "miso", "cnt (lead)");
      $sformat(line, "%-14s | %-12.2f | 0x%02h | 0x%02h | %d\n",
                    t.mt, t.tran_time_start, t.mosi, t.miso, t.curr_lead);
      `uvm_info("SCB", hdr, UVM_NONE);
      `uvm_info("SCB", line, UVM_NONE);
      $fdisplay(log_fd, hdr);
      $fdisplay(log_fd, line);        
      $fclose(log_fd); 
    end 
    else if (mode == 1) begin 
      log_fd   = $fopen("scoreboard_log_OL0HA1_L.txt", "a");
      if (!log_fd) `uvm_fatal("SCB", "Cannot open scoreboard_log.txt");
      $sformat(hdr,  "%-14s | %-12s | %-8s | %-8s",
                    "type", "start time", "mosi", "cnt (lead)");
      $sformat(line, "%-14s | %-12.2f | 0x%02h | %d\n",
                    t.mt, t.tran_time_start, t.mosi, t.curr_lead);
      `uvm_info("SCB", hdr, UVM_NONE);
      `uvm_info("SCB", line, UVM_NONE);
      $fdisplay(log_fd, hdr);
      $fdisplay(log_fd, line);        
      $fclose(log_fd); 
    end 
    else if (mode == 2) begin   
      log_fd   = $fopen("scoreboard_log_OL0HA1_T.txt", "a");
      if (!log_fd) `uvm_fatal("SCB", "Cannot open scoreboard_log.txt");
      $sformat(hdr,  "%-14s | %-12s | %-8s | %-8s",
                    "type", "start time", "miso", "cnt (lead)");
      $sformat(line, "%-14s | %-12.2f | 0x%02h | %d\n",
                    t.mt, t.tran_time_start, t.miso, t.curr_fall);
      `uvm_info("SCB", hdr, UVM_NONE);
      `uvm_info("SCB", line, UVM_NONE);
      $fdisplay(log_fd, hdr);
      $fdisplay(log_fd, line);        
      $fclose(log_fd); 
    end 
    else if (mode == 3) begin 
      log_fd   = $fopen("scoreboard_log_OL1HA0.txt", "a");
      if (!log_fd) `uvm_fatal("SCB", "Cannot open scoreboard_log.txt");

      $sformat(hdr,  "%-14s | %-12s | %-8s | %-8s | %-8s",
                    "type", "start time", "mosi", "miso", "cnt (lead)");
      $sformat(line, "%-14s | %-12.2f | 0x%02h | 0x%02h | %d\n",
                    t.mt, t.tran_time_start, t.mosi, t.miso, t.curr_lead);
      `uvm_info("SCB", hdr, UVM_NONE);
      `uvm_info("SCB", line, UVM_NONE);
      $fdisplay(log_fd, hdr);
      $fdisplay(log_fd, line);        
      $fclose(log_fd); 
    end 
    else if (mode == 4) begin 
      log_fd   = $fopen("scoreboard_log_OL1HA1_L.txt", "a");
      if (!log_fd) `uvm_fatal("SCB", "Cannot open scoreboard_log.txt");
      $sformat(hdr,  "%-14s | %-12s | %-8s | %-8s",
                    "type", "start time", "miso", "cnt (lead)");
      $sformat(line, "%-14s | %-12.2f | 0x%02h | %d\n",
                    t.mt, t.tran_time_start, t.miso, t.curr_lead);
      `uvm_info("SCB", hdr, UVM_NONE);
      `uvm_info("SCB", line, UVM_NONE);
      $fdisplay(log_fd, hdr);
      $fdisplay(log_fd, line);        
      $fclose(log_fd); 
    end 
    else if (mode == 5) begin 
      log_fd   = $fopen("scoreboard_log_OL1HA1_T.txt", "a");
      if (!log_fd) `uvm_fatal("SCB", "Cannot open scoreboard_log.txt");
      $sformat(hdr,  "%-14s | %-12s | %-8s | %-8s",
                    "type", "start time", "mosi", "cnt (lead)");
      $sformat(line, "%-14s | %-12.2f | 0x%02h | %d\n",
                    t.mt, t.tran_time_start, t.mosi, t.curr_fall);
      `uvm_info("SCB", hdr, UVM_NONE);
      `uvm_info("SCB", line, UVM_NONE);
      $fdisplay(log_fd, hdr);
      $fdisplay(log_fd, line);        
      $fclose(log_fd); 
    end
    else begin 
      `uvm_error("SCB", $sformatf("Wrong usage of print_OLHA function"));
    end

  endfunction



  // T015: Check entire transaction correctness by reporting uvm_error 
  function void print_entire(spi_tran t);
    string hdr, line;
    log_fd   = $fopen("scoreboard_log_entire.txt", "a");
    if (!log_fd) `uvm_fatal("SCB", "Cannot open scoreboard_log.txt");
    // T015: Check TX and RX value match
    if (slave_reset_response === t.rx_data) begin 
      `uvm_info("SCB", $sformatf("T015 satisfied: RX data match expected slave response (SLAVE RESET RESP)"), UVM_LOW);
    end else begin 
      `uvm_error("SCB", $sformatf("T015 violated: RX data mismatch expected slave response (SLAVE RESET RESP)"));
    end
    $sformat(hdr,  "%-12s | %-12s | %-8s | %-8s | %-8s",
                    "start time", "end time", "ID", "TX", "RX");
    $sformat(line, "%-12.2f | %-12.2f | %-8d | 0x%02h | 0x%02h\n",
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
      `uvm_info("SCB", $sformatf("T001 and T002 satisfied: New transaction cannot start when busy is HIGH."), UVM_LOW);
    end else if (mosimiso == 0) begin 
      `uvm_error("SCB", $sformatf("T001 and T002 violated:  New transaction started when busy is HIGH."));
    end
    // T024: Check mosi/miso value match
    if ((mosimiso == 0) && (t.tx_data_t024 === t.MS_data)) begin 
      `uvm_info("SCB", $sformatf("T024 satisfied: Data from MOSI matches slave_rx_data on done posedge."), UVM_LOW);
    end else if (mosimiso == 0) begin 
      `uvm_error("SCB", $sformatf("T024 violated: Data from MOSI mismatch slave_rx_data on done posedge."));
    end
    $sformat(hdr,  "%-12s | %-12s | %-8s | %-8s",
                    "start time", "end time", "ID", (mosimiso) ? "miso" : "mosi");
    $sformat(line, "%-12.2f | %-12.2f | %-8d | 0x%02h\n",
                    t.tran_time_start, t.tran_time_end, t.tran_id, t.MS_data);
    `uvm_info("SCB", hdr, UVM_NONE);
    `uvm_info("SCB", line, UVM_NONE);
    $fdisplay(log_fd, hdr);
    $fdisplay(log_fd, line);
    $fclose(log_fd);
  endfunction

  function void check_T021(spi_tran tr);
  // If reset is asserted (reset == 0), check that SPI signals immediately go to idle
    if (tr.rst_n === 0) begin
      if ((tr.busy !== 0) || (tr.cs_n !== 1) || (tr.sclk !== 0)) begin
        `uvm_error("SCB", $sformatf("T021 violated during reset: busy=%0b, cs_n=%0b, sclk=%0b",
                                    tr.busy, tr.cs_n, tr.sclk));
      end else begin
        `uvm_info("SCB", $sformatf("T021 satisfied during reset: busy=%0b, cs_n=%0b, sclk=%0b",
                                  tr.busy, tr.cs_n, tr.sclk), UVM_LOW);
      end
    end else begin
       `uvm_info("SCB", "T021 not applicable: reset is not asserted, no check performed.", UVM_LOW);
    end
  endfunction

  function void check_T022(spi_tran tr);

  // True violation: start is triggered while done is still high
  if ((tr.done === 1) && (tr.start === 1)) begin
    `uvm_error("SCB", $sformatf("T022 VIOLATION: Start asserted while 'done' is high. \
start=%0b, done=%0b, time=%0t", tr.start, tr.done, $time));
  end
  else if (tr.done === 1) begin
    `uvm_info("SCB", $sformatf("T022 OK: 'done' seen cleanly without start overlap. time=%0t", $time), UVM_LOW);
  end

  endfunction

  function void report_phase (uvm_phase phase);
    check_checkeray();
  endfunction
endclass

