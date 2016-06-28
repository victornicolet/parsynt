open Printf

let port_no = 9877
let server_name = "localhost"

let main_client client_fun  =
  if Array.length Sys.argv < 3
  then printf "usage :  client server port\n"
  else let server = Sys.argv.(1) in
       let server_addr =
         try  Unix.inet_addr_of_string server
         with Failure("inet_addr_of_string") ->
           try  (Unix.gethostbyname server).Unix.h_addr_list.(0)
           with Not_found ->
             eprintf "%s : Unknown server\n" server ;
             exit 2
       in try
            let port = int_of_string (Sys.argv.(2)) in
            let sockaddr = Unix.ADDR_INET(server_addr,port) in
            while true do
              let ic,oc = Unix.open_connection sockaddr
              in
              client_fun ic oc ;
              Unix.shutdown_connection ic;
            done
         with Failure("int_of_string") -> eprintf "bad port number";
           exit 2 ;;

let shut_exit ic oc exn =
  Unix.shutdown_connection ic;
  match exn with
  | Exit -> exit 0
  | _ -> raise exn

let client_fun ic oc =
  try
    print_string  "Request : " ;
    flush stdout ;
    let inp = input_line stdin in
    output_string oc (inp^"\n") ;
    flush oc ;
    if inp = "END" then shut_exit ic oc Exit;
    let response = input_line ic
    in printf "Response : %s\n\n" response;
    if response = "END" then shut_exit ic oc Exit;
  with
  | exn -> shut_exit ic oc exn

let synthpb =
  "(begin
     (define-symbolic a integer?)\
     (define (f x) ((choose + - / *) 1 x))\
     (define odot (synthesize  #:forall (list a) #:guarantee (= (f a) a))))"

let test_send_synthpb ic oc =
  try
    print_string  "Request : " ;
    flush stdout;
    output_string oc synthpb ;
    flush oc ;
    let response = input_line ic in
    printf "Response : %s\n\n" response;
    shut_exit ic oc Exit;
  with
  | exn -> shut_exit ic oc exn

let go_client () = main_client client_fun ;;

let go_test_synthpb () = main_client test_send_synthpb;;


go_test_synthpb ();;
(**go_client ();;*)
