use std::collections::BTreeMap;
use std::convert::TryInto;
use std::path::PathBuf;

use clap::{App, Arg};
use serde::Deserialize;

use filecoin_proofs::{PoStType, PrivateReplicaInfo, PublicReplicaInfo, with_shape, generate_winning_post, generate_window_post, verify_window_post, verify_winning_post};
use filecoin_proofs::constants::WINDOW_POST_CHALLENGE_COUNT;
use storage_proofs::merkle::MerkleTreeTrait;
use storage_proofs::sector::SectorId;
use storage_proofs::hasher::{Domain, Hasher};
use storage_proofs::compound_proof::{SetupParams, CompoundProof, PublicParams};
use storage_proofs::post::fallback;
use log::{SetLoggerError, LevelFilter, Record, Level, Metadata, info};

use filecoin_proofs::types::{ChallengeSeed, PoStConfig, ProverId, SectorSize};
use storage_proofs::fr32::bytes_into_fr;
use rayon::prelude::*;
use std::time::SystemTime;

use anyhow::{ensure, Context, Result};

use filecoin_proofs::parameters::{window_post_setup_params, winning_post_setup_params};
use storage_proofs::proof::ProofScheme;
// use filecoin_proofs::api::util::{as_safe_commitment, get_base_tree_leafs, get_base_tree_size};

const SECTOR_SIZE_32_GIB: u64 = 32 * 1024 * 1024 * 1024;
const SECTOR_SIZE_512_MIB: u64 = 512 * 1024 * 1024;

struct SimpleLogger;

impl log::Log for SimpleLogger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= Level::Info
    }

    fn log(&self, record: &Record) {
        if self.enabled(record.metadata()) {
            println!("{} - {}", record.level(), record.args());
        }
    }

    fn flush(&self) {}
}

fn init_log() -> Result<(), SetLoggerError> {
    log::set_boxed_logger(Box::new(SimpleLogger))
        .map(|()| log::set_max_level(LevelFilter::Info))
}

#[derive(Deserialize, Debug)]
pub struct Config {
    prefix: String,
    miner_id: u64,
    sector_id: u64,
    challenge_count: usize,
    comm_r: String,
    prover: String,
    randomness: String,
}

fn load_conf(config: &str) -> std::io::Result<Config> {
    let v = std::fs::read(config)?;
    let conf: Config = serde_json::from_slice(&v).unwrap();
    return Ok(conf);
}

fn decode_u8_32(s: &str) -> [u8; 32] {
    let d = base64_url::decode(s).expect("invalid data");
    println!("length {}", d.len());
    let b: [u8; 32] = d.as_slice().try_into().expect("Size is not 32");
    b
}

fn main() {
    let matches = App::new("Single POST")
        .version("0.1")
        .author("bailong")
        .about("repeat post verify")
        .arg(Arg::with_name("param")
            .short("p")
            .long("param")
            .value_name("withParam")
            .help("set with param cache")
            .takes_value(false))
        .arg(Arg::with_name("config")
            .short("c")
            .long("config")
            .value_name("FILE")
            .help("Sets a custom config file")
            .takes_value(true))
        .get_matches();
    init_log();
    let param = matches.is_present("param");
    let config = matches.value_of("config").unwrap_or("default.conf");
    println!("config: {}", config);
    let conf = load_conf(config).expect("load config failed");

    let prefix = conf.prefix;
    let miner_id = conf.miner_id;
    let sector_id = conf.sector_id;
    let challenge_count = conf.challenge_count;
    let typ = if challenge_count == WINDOW_POST_CHALLENGE_COUNT {
        PoStType::Window
    } else {
        PoStType::Winning
    };

    let comm_r = decode_u8_32(&conf.comm_r);
    let prover = decode_u8_32(&conf.prover);
    let randomness = decode_u8_32(&conf.randomness);
    let r = with_shape!(
        SECTOR_SIZE_32_GIB,
        post,
        &prefix,
        miner_id,
        sector_id,
        challenge_count,
        typ,
        comm_r,
        prover,
        randomness,
        param,
    );
    println!("done. {:?} error {:?}", r, r.as_ref().err());
}

fn seal_file(prefix: &str, miner_id: u64, sector_id: u64) -> PathBuf {
    let s = format!("{}/sealed/s-t0{}-{}", prefix, miner_id, sector_id);
    PathBuf::from(s)
}

fn cache_dir(prefix: &str, miner_id: u64, sector_id: u64) -> PathBuf {
    let s = format!("{}/cache/s-t0{}-{}", prefix, miner_id, sector_id);
    PathBuf::from(s)
}

fn post<Tree: 'static + MerkleTreeTrait>(
    prefix: &str,
    minder_id: u64,
    sector_id: u64,
    challenge_count: usize,
    typ: PoStType,
    comm_r: [u8; 32],
    prover: [u8; 32],
    randomness: [u8; 32],
    withParam: bool,
) -> Result<bool> {
    let sector_size = SectorSize(SECTOR_SIZE_32_GIB);
    let sealed_file_path = seal_file(prefix, minder_id, sector_id);
    let cache_dir = cache_dir(prefix, minder_id, sector_id);
    let sector_id = SectorId::from(sector_id);

    let is_window = typ == PoStType::Window;
    let post_config = PoStConfig {
        sector_size,
        challenge_count,
        sector_count: 1,
        typ,
        priority: true,
    };

    let r = if is_window {
        let pub_replica = PublicReplicaInfo::new(comm_r).expect("failed to create public replica info");
        let priv_replica = PrivateReplicaInfo::<Tree>::new(sealed_file_path, comm_r, cache_dir.clone())
            .expect("failed to create private replica info");
        // Store the replica's private and publicly facing info for proving and verifying respectively.
        let mut pub_replica_info: BTreeMap<SectorId, PublicReplicaInfo> = BTreeMap::new();
        let mut priv_replica_info: BTreeMap<SectorId, PrivateReplicaInfo<Tree>> = BTreeMap::new();

        pub_replica_info.insert(sector_id, pub_replica);
        priv_replica_info.insert(sector_id, priv_replica);

        let ret = if withParam {
            let x = generate_window_post::<Tree>(
                &post_config, &randomness, &priv_replica_info, prover)?;
            verify_window_post::<Tree>(
                &post_config, &randomness, &pub_replica_info, prover, &x)
        } else {
            generate_window_post_blank::<Tree>(
                &post_config, &randomness, &priv_replica_info, prover)
        };
        ret
    } else {
        let pub_replica = PublicReplicaInfo::new(comm_r).expect("failed to create public replica info");
        let priv_replica = PrivateReplicaInfo::<Tree>::new(sealed_file_path, comm_r, cache_dir.clone())
            .expect("failed to create private replica info");
        let pub_replica_info = vec![(sector_id, pub_replica)];
        let priv_replica_info = vec![(sector_id, priv_replica)];

        let ret = if withParam {
            let x = generate_winning_post::<Tree>(
                &post_config, &randomness, &priv_replica_info[..], prover)?;
            verify_winning_post::<Tree>(
                &post_config, &randomness, &pub_replica_info[..], prover, &x)
        }else {
            generate_winning_post_blank::<Tree>(
                &post_config, &randomness, &priv_replica_info[..], prover)
        };
        ret
    };
    r
}

fn as_safe_commitment<H: Domain, T: AsRef<str>>(
    comm: &[u8; 32],
    commitment_name: T,
) -> Result<H> {
    bytes_into_fr(comm)
        .map(Into::into)
        .with_context(|| format!("Invalid commitment ({})", commitment_name.as_ref(),))
}

fn generate_window_post_blank<Tree: 'static + MerkleTreeTrait>(
    post_config: &PoStConfig,
    randomness: &ChallengeSeed,
    replicas: &BTreeMap<SectorId, PrivateReplicaInfo<Tree>>,
    prover_id: ProverId,
) -> Result<bool> {
    let timestamp = SystemTime::now();
    info!("generate_window_post:start");
    ensure!(
        post_config.typ == PoStType::Window,
        "invalid post config type"
    );
    info!("thread counts {}", rayon::current_num_threads());
    let randomness_safe = as_safe_commitment(randomness, "randomness")?;
    let prover_id_safe = as_safe_commitment(&prover_id, "prover_id")?;

    let vanilla_params = window_post_setup_params(&post_config);
    let partitions = Some(1 as usize);

    let sector_count = vanilla_params.sector_count;
    let setup_params = SetupParams {
        vanilla_params,
        partitions,
        priority: post_config.priority,
    };

    let pub_params: PublicParams<fallback::FallbackPoSt<Tree>> =
        fallback::FallbackPoStCompound::setup(&setup_params)?;
    let t2 = SystemTime::now();
    let trees: Vec<_> = replicas
        .par_iter()
        .map(|(_id, replica)| replica.merkle_tree(post_config.sector_size))
        .collect::<Result<_>>()?;
    info!("window init tree {} qiniu-time {:?}", trees.len(), t2.elapsed());
    let mut pub_sectors = Vec::with_capacity(sector_count);
    let mut priv_sectors = Vec::with_capacity(sector_count);

    for ((sector_id, replica), tree) in replicas.iter().zip(trees.iter()) {
        let comm_r = replica.safe_comm_r()?;
        let comm_c = replica.safe_comm_c();
        let comm_r_last = replica.safe_comm_r_last();

        pub_sectors.push(fallback::PublicSector {
            id: *sector_id,
            comm_r,
        });
        priv_sectors.push(fallback::PrivateSector {
            tree,
            comm_c,
            comm_r_last,
        });
    }

    let pub_inputs = fallback::PublicInputs {
        randomness: randomness_safe,
        prover_id: prover_id_safe,
        sectors: &pub_sectors,
        k: None,
    };

    let priv_inputs = fallback::PrivateInputs::<Tree> {
        sectors: &priv_sectors,
    };
    let vanilla_proofs = fallback::FallbackPoSt::<Tree>::prove_all_partitions(
        &pub_params.vanilla_params,
        &pub_inputs,
        &priv_inputs,
        1,
    )?;

    let sanity_check = fallback::FallbackPoSt::<Tree>::verify_all_partitions(&pub_params.vanilla_params, &pub_inputs, &vanilla_proofs)?;
    ensure!(sanity_check, "sanity check failed");

    info!("generate_window_post:finish {:?}", timestamp.elapsed());

    Ok(sanity_check)
}

fn generate_winning_post_blank<Tree: 'static + MerkleTreeTrait>(
    post_config: &PoStConfig,
    randomness: &ChallengeSeed,
    replicas: &[(SectorId, PrivateReplicaInfo<Tree>)],
    prover_id: ProverId,
) -> Result<bool> {
    let timestamp = SystemTime::now();
    info!("generate_winning_post:start");
    ensure!(
        post_config.typ == PoStType::Winning,
        "invalid post config type"
    );

    ensure!(
        replicas.len() == post_config.sector_count,
        "invalid amount of replicas"
    );

    let randomness_safe: <Tree::Hasher as Hasher>::Domain =
        as_safe_commitment(randomness, "randomness")?;
    let prover_id_safe: <Tree::Hasher as Hasher>::Domain =
        as_safe_commitment(&prover_id, "prover_id")?;

    let vanilla_params = winning_post_setup_params(&post_config)?;
    let param_sector_count = vanilla_params.sector_count;

    let setup_params = SetupParams {
        vanilla_params,
        partitions: None,
        priority: post_config.priority,
    };
    let pub_params: PublicParams<fallback::FallbackPoSt<Tree>> =
        fallback::FallbackPoStCompound::setup(&setup_params)?;
    let t2 = SystemTime::now();
    let trees = replicas
        .par_iter()
        .map(|(_, replica)| replica.merkle_tree(post_config.sector_size))
        .collect::<Result<Vec<_>>>()?;
    info!("winning init tree {} qiniu-time {:?}", trees.len(), t2.elapsed());
    let mut pub_sectors = Vec::with_capacity(param_sector_count);
    let mut priv_sectors = Vec::with_capacity(param_sector_count);

    for _ in 0..param_sector_count {
        for ((id, replica), tree) in replicas.iter().zip(trees.iter()) {
            let comm_r = replica.safe_comm_r()?;
            let comm_c = replica.safe_comm_c();
            let comm_r_last = replica.safe_comm_r_last();

            pub_sectors.push(fallback::PublicSector::<<Tree::Hasher as Hasher>::Domain> {
                id: *id,
                comm_r,
            });
            priv_sectors.push(fallback::PrivateSector {
                tree,
                comm_c,
                comm_r_last,
            });
        }
    }

    let pub_inputs = fallback::PublicInputs::<<Tree::Hasher as Hasher>::Domain> {
        randomness: randomness_safe,
        prover_id: prover_id_safe,
        sectors: &pub_sectors,
        k: None,
    };

    let priv_inputs = fallback::PrivateInputs::<Tree> {
        sectors: &priv_sectors,
    };

    let vanilla_proofs = fallback::FallbackPoSt::<Tree>::prove_all_partitions(
        &pub_params.vanilla_params,
        &pub_inputs,
        &priv_inputs,
        1,
    )?;

    let sanity_check = fallback::FallbackPoSt::<Tree>::verify_all_partitions(&pub_params.vanilla_params, &pub_inputs, &vanilla_proofs)?;
    ensure!(sanity_check, "sanity check failed");

    info!("generate_winning_post:finish {:?}", timestamp.elapsed());
    Ok(sanity_check)
}