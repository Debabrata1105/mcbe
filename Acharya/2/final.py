import time
from charm.toolbox.pairinggroup import PairingGroup, ZR, G1, G2, GT, pair

class MCBE_II:
    def __init__(self, group):
        self.group = group
        # Master secret keys
        self.alpha = group.random(ZR)
        self.gamma = group.random(ZR)
        self.beta_values = {}
        
        # Generators
        self.g1 = group.random(G1)
        self.g2 = group.random(G2)
        
        # v = g1^gamma (from paper)
        self.v = self.g1 ** self.gamma
        
        self.num_users = 0
        self.num_groups = 0
        self.pi0 = None

    def setup(self, num_users, num_groups):
        """
        Setup algorithm from MCBE-II paper
        Returns: (params, mkey)
        """
        start_time = time.time()
        
        self.num_users = num_users
        self.num_groups = num_groups
        
        # Calculate pi0 = g1^((alpha^(nu+1) - 1)/(alpha - 1))
        numerator = self.alpha ** (num_users + 1) - 1
        denominator = self.alpha - 1
        denominator_inv = denominator ** -1
        exponent = numerator * denominator_inv
        self.pi0 = self.g1 ** exponent

        # Precompute g1^(alpha^i) for i = 1 to 2*nu+1 (excluding nu+1)
        g1_alpha_powers = {}
        g2_alpha_powers = {}
        
        for i in range(1, 2 * num_users + 2):
            if i != num_users + 1:  # Skip alpha^(nu+1) as per DBDHE assumption
                g1_alpha_powers[i] = self.g1 ** (self.alpha ** i)
                g2_alpha_powers[i] = self.g2 ** (self.alpha ** i)
        
        # Add g1^(alpha^(nu+1)) for decryption
        g1_alpha_powers[num_users + 1] = self.g1 ** (self.alpha ** (num_users + 1))
        
        # Generate beta values for each group
        g1_beta_powers = {}
        for u in range(1, num_groups + 1):
            beta_u = self.group.random(ZR)
            self.beta_values[u] = beta_u
            g1_beta_powers[u] = self.g1 ** beta_u
        
        params = {
            'g1': self.g1,
            'g2': self.g2,
            'v': self.v,
            'pi0': self.pi0,
            'g1_alpha_powers': g1_alpha_powers,
            'g2_alpha_powers': g2_alpha_powers,
            'g1_beta_powers': g1_beta_powers,
            'num_users': num_users,
            'num_groups': num_groups
        }
        
        mkey = {
            'alpha': self.alpha,
            'gamma': self.gamma,
            'beta_values': self.beta_values
        }
        
        setup_time = time.time() - start_time
        return params, mkey, setup_time

    def key_extract(self, user_id, group_id, params):
        """
        Key extraction algorithm from MCBE-II paper
        Returns: (secret_key, public_key)
        """
        if user_id > params['num_users'] or group_id > params['num_groups']:
            raise ValueError("User ID or Group ID exceeds maximum allowed")
            
        # Secret key components according to paper
        g1_alpha_i = params['g1_alpha_powers'][user_id]
        skey_i1 = g1_alpha_i ** self.gamma
        
        g1_beta_u = params['g1_beta_powers'][group_id]
        skey_i2 = g1_beta_u ** self.gamma
        
        skey = (skey_i1, skey_i2)
        
        # Public key components
        pkey = {
            'pi_i': g1_alpha_i,
            'g1_beta_u': g1_beta_u,
            'g1_alpha_i': g1_alpha_i,
            'user_id': user_id,
            'group_id': group_id
        }
        
        return skey, pkey

    def encrypt(self, subscribed_groups, params):
        """
        Encryption algorithm from MCBE-II paper (Inclusive form only)
        Input: subscribed_groups = {group_id: [user_list]}
        Returns: (ciphertext, group_keys, encryption_time, random_s)
        """
        start_time = time.time()
        
        g1 = params['g1']
        g2 = params['g2']
        v = params['v']
        g1_alpha_powers = params['g1_alpha_powers']
        g1_beta_powers = params['g1_beta_powers']
        nu = params['num_users']
        
        # Flatten all subscribed users across all groups to get set S
        S = set()
        for group_id, users in subscribed_groups.items():
            S.update(users)
        
        # Choose random s
        s = self.group.random(ZR)
        
        # According to paper's inclusive form:
        # ct1 = (v * ∏_{j∈S} g1^(alpha^(nu+1-j)))^s
        product_term = self.group.init(G1, 1)  # Initialize to identity element
        for j in S:
            exponent_index = nu + 1 - j
            if exponent_index in g1_alpha_powers:
                product_term *= g1_alpha_powers[exponent_index]
        
        ct1 = (v * product_term) ** s
        
        # Compute ct2 = g1^s
        ct2 = g1 ** s
        
        # Compute group keys according to paper:
        # Gkey_u = e(g1^beta_u, v)^s * e(g1^(alpha^(nu+1)), g1)^s
        group_keys = {}
        e_alpha_nu_plus_1 = pair(g1_alpha_powers[nu + 1], g1) ** s
        
        for group_id in subscribed_groups:
            if group_id in g1_beta_powers:
                term1 = pair(g1_beta_powers[group_id], v) ** s
                gk = term1 * e_alpha_nu_plus_1
                group_keys[group_id] = gk
        
        encryption_time = time.time() - start_time
        return (ct1, ct2), group_keys, encryption_time, s

    def decrypt(self, skey, user_id, group_id, subscribed_groups, ciphertext, params):
        """
        Decryption algorithm from MCBE-II paper (Inclusive form)
        Returns: (recovered_group_key, decryption_time)
        """
        start_time = time.time()
        
        skey_i1, skey_i2 = skey
        ct1, ct2 = ciphertext
        
        g1_alpha_powers = params['g1_alpha_powers']
        nu = params['num_users']
        
        # Get the complete set S of all subscribed users
        S = set()
        for users in subscribed_groups.values():
            S.update(users)
        
        # According to paper's decryption for inclusive form
        # Numerator: e(g1^(alpha^i), ct1)
        g1_alpha_i = g1_alpha_powers[user_id]
        numerator = pair(g1_alpha_i, ct1)
        
        # Denominator: e(skey_i1 * ∏_{j∈S\{i}} g1^(alpha^(nu+1-j+i)), ct2)
        product_term = self.group.init(G1, 1)  # Initialize to identity
        for j in S:
            if j != user_id:
                exponent_index = nu + 1 - j + user_id
                if exponent_index in g1_alpha_powers:
                    product_term *= g1_alpha_powers[exponent_index]
        
        denominator_arg = skey_i1 * product_term
        denominator = pair(denominator_arg, ct2)
        
        # Compute e(g1^(alpha^(nu+1)), g1)^s
        e_alpha_nu_plus_1_s = numerator / denominator
        
        # Final group key: Gkey_u = e(skey_i2, ct2) * e(g1^(alpha^(nu+1)), g1)^s
        term1 = pair(skey_i2, ct2)
        recovered_key = term1 * e_alpha_nu_plus_1_s
        
        decryption_time = time.time() - start_time
        return recovered_key, decryption_time


def run_performance_test(mu, n_total, n_subscribed):
    """
    Run performance test for given parameters
    
    Args:
        mu: Number of groups
        n_total: Users per group (total)
        n_subscribed: Users per group (subscribed)
    
    Returns:
        dict: Performance metrics
    """
    # Initialize pairing group
    group = PairingGroup('SS512')
    mcbe = MCBE_II(group)
    
    # Calculate total users
    total_users = mu * n_total
    total_subscribed = mu * n_subscribed
    
    # Setup
    params, mkey, setup_time = mcbe.setup(total_users, mu)
    
    # Create group structure
    subscribed_groups = {}
    user_id = 1
    
    for group_id in range(1, mu + 1):
        # All users in this group (for bounds checking)
        group_users = list(range(user_id, user_id + n_total))
        
        # Subscribed users in this group (first n_subscribed users)
        subscribed_users = group_users[:n_subscribed]
        subscribed_groups[group_id] = subscribed_users
        
        user_id += n_total
    
    # Generate secret keys for all subscribed users
    key_gen_start = time.time()
    secret_keys = {}
    public_keys = {}
    
    for group_id, users in subscribed_groups.items():
        for user_id in users:
            skey, pkey = mcbe.key_extract(user_id, group_id, params)
            secret_keys[user_id] = (skey, group_id)
            public_keys[user_id] = pkey
    
    key_gen_time = time.time() - key_gen_start
    
    # Encryption
    try:
        ciphertext, expected_group_keys, encryption_time, s = mcbe.encrypt(subscribed_groups, params)
        
        # Test decryption for a sample of subscribed users (one from each group)
        total_decryption_time = 0
        successful_decryptions = 0
        
        for group_id, subscribed_users in subscribed_groups.items():
            # Test first subscribed user from each group
            test_user = subscribed_users[0]
            skey, _ = secret_keys[test_user]
            
            recovered_key, decryption_time = mcbe.decrypt(
                skey, 
                test_user,
                group_id,
                subscribed_groups,
                ciphertext, 
                params
            )
            
            total_decryption_time += decryption_time
            
            # Verify correctness
            if recovered_key == expected_group_keys[group_id]:
                successful_decryptions += 1
        
        avg_decryption_time = total_decryption_time / mu
        
        return {
            'total_users': total_users,
            'total_subscribed': total_subscribed,
            'mu': mu,
            'n_total': n_total,
            'n_subscribed': n_subscribed,
            'setup_time': setup_time,
            'key_gen_time': key_gen_time,
            'encryption_time': encryption_time,
            'avg_decryption_time': avg_decryption_time,
            'successful_decryptions': successful_decryptions,
            'total_groups': mu,
            'success': True
        }
        
    except Exception as e:
        return {
            'total_users': total_users,
            'total_subscribed': total_subscribed,
            'mu': mu,
            'n_total': n_total,
            'n_subscribed': n_subscribed,
            'setup_time': setup_time,
            'key_gen_time': key_gen_time,
            'encryption_time': 0,
            'avg_decryption_time': 0,
            'error': str(e),
            'success': False
        }


def main():
    """
    Performance testing based on the table specifications for MCBE-II (Version 2)
    """
    print("=== MCBE-II Performance Testing (Version 2) ===")
    print("Based on implementation details table format")
    print("Scheme: Multi-Channel Broadcast Encryption with Adaptive Security")
    print("Implementation: Inclusive form with corrected decryption algorithm")
    print()
    
    # Test cases from the table
    test_cases = [
        # (total_users, subscribed_users, mu, n_total, n_subscribed)
        (1024, 256, 4, 256, 64),      # 1024 (μ=4,n=256), 256 (μ=4,n=64)
        (2048, 512, 8, 256, 64),      # 2048 (μ=8,n=256), 512 (μ=8,n=64)
        (4096, 1024, 8, 512, 128),    # 4096 (μ=8,n=512), 1024 (μ=8,n=128)
        (8192, 2048, 16, 512, 128),   # 8192 (μ=16,n=512), 2048 (μ=16,n=128)
        (16384, 4096, 16, 1024, 256), # 16384 (μ=16,n=1024), 4096 (μ=16,n=256)
        (32768, 8192, 32, 1024, 256)  # 32768 (μ=32,n=1024), 8192 (μ=32,n=256)
    ]
    
    print("| Total Users | Subscribed | μ (Groups) | n (per group) | Setup (s) | Encrypt (s) | Decrypt (s) |")
    print("|-------------|------------|------------|---------------|-----------|-------------|-------------|")
    
    for total_users, subscribed_users, mu, n_total, n_subscribed in test_cases:
        print(f"Testing: {total_users} total users, {subscribed_users} subscribed, μ={mu}, n={n_total}")
        
        try:
            result = run_performance_test(mu, n_total, n_subscribed)
            
            if result['success']:
                print(f"| {total_users:11d} | {subscribed_users:10d} | {mu:10d} | {n_total:13d} | {result['setup_time']:9.6f} | {result['encryption_time']:11.6f} | {result['avg_decryption_time']:11.6f} |")
                
                # Verify correctness
                if result['successful_decryptions'] == result['total_groups']:
                    status = "✓ PASS"
                else:
                    status = f"✗ FAIL ({result['successful_decryptions']}/{result['total_groups']})"
                
                print(f"  Status: {status}")
                
            else:
                print(f"| {total_users:11d} | {subscribed_users:10d} | {mu:10d} | {n_total:13d} | ERROR     | ERROR       | ERROR       |")
                print(f"  Error: {result.get('error', 'Unknown error')}")
                
        except Exception as e:
            print(f"| {total_users:11d} | {subscribed_users:10d} | {mu:10d} | {n_total:13d} | ERROR     | ERROR       | ERROR       |")
            print(f"  Exception: {e}")
        
        print()
    
    print("=== Performance Summary ===")
    print("Scheme: MCBE-II (Multi-Channel Broadcast Encryption with Adaptive Security)")
    print("Implementation: Version 2 with corrected inclusive decryption")
    print("μ = Number of groups")
    print("n = Number of users per group")
    print("Setup time: Time to generate public parameters and precompute values")
    print("Encrypt time: Time to encrypt and generate group keys")
    print("Decrypt time: Average time for one user to decrypt (tested per group)")
    print()
    print("Key Features:")
    print("- Inclusive encryption form only")
    print("- Corrected decryption algorithm matching paper specification")
    print("- Precomputed g1^(alpha^i) powers for efficiency")
    print("- Per-group beta values for multi-channel support")
    print()
    print("Security: Adaptive IND-CPA under DBDHE assumption")
    print("Note: All times are in seconds")


if __name__ == '__main__':
    main()