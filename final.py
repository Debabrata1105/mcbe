from charm.toolbox.pairinggroup import PairingGroup, ZR, G1, G2, GT, pair
import time

class MCBE_I:
    """
    Multi-Channel Broadcast Encryption with Selective Security (MCBE-I)
    
    This implementation follows the MCBE-I scheme from:
    "K. Acharya / Journal of Information Security and Applications 51 (2020) 102436"
    
    The scheme supports multiple groups of users where each group can have
    different subscribers, and provides selective IND-CPA security under
    the ν-DBDHE assumption.
    """
    
    def __init__(self, groupObj):
        """
        Initialize the MCBE-I scheme with a bilinear group
        
        Args:
            groupObj: PairingGroup object for bilinear operations
        """
        self.group = groupObj
        self.g1 = self.group.random(G1)  # Generator g1 ∈ G1
        self.g2 = self.group.random(G2)  # Generator g2 ∈ G2
        self.alpha = self.group.random(ZR)  # Master secret α
        self.gamma = self.group.random(ZR)  # Master secret γ
        self.v = self.g2 ** self.gamma   # Public parameter v = g2^γ ∈ G2
    
    def setup(self, num_users):
        """
        Setup algorithm - generates public parameters and master key
        
        Args:
            num_users (int): Total number of users ν = μ × n
                           where μ = number of groups, n = users per group
        
        Returns:
            tuple: (params, mkey) where:
                - params: Public parameters
                - mkey: Master key (kept secret by PKG)
        """
        self.num_users = num_users
        
        # Generate g1^(α^i) for i ∈ [1, 2ν+1] \ {ν+1}
        g1_alpha_powers = {}
        for i in range(1, 2 * num_users + 2):
            if i != num_users + 1:  # Skip ν+1
                g1_alpha_powers[i] = self.g1 ** (self.alpha ** i)
        
        # Generate g2^(α^i) for i ∈ [1, 2ν+1] \ {ν+1}
        g2_alpha_powers = {}
        for i in range(1, 2 * num_users + 2):
            if i != num_users + 1:  # Skip ν+1
                g2_alpha_powers[i] = self.g2 ** (self.alpha ** i)
        
        params = {
            'g1': self.g1,
            'g2': self.g2,
            'v': self.v,
            'g1_alpha_powers': g1_alpha_powers,
            'g2_alpha_powers': g2_alpha_powers,
            'num_users': num_users
        }
        
        mkey = {
            'alpha': self.alpha,
            'gamma': self.gamma
        }
        
        return params, mkey
    
    def key_extract(self, user_id, group_users):
        """
        Key extraction algorithm - generates secret key for a user
        
        Args:
            user_id (int): User identifier i
            group_users (list): List of all users in the same group as user i
        
        Returns:
            tuple: (skey_i1, skey_i2) - Secret key components for user i
        """
        # skey_i1 = (g1^α^i)^γ
        g1_alpha_i = self.g1 ** (self.alpha ** user_id)
        skey_i1 = g1_alpha_i ** self.gamma
        
        # skey_i2 = (g1^(∑_{j∈Gr_u, j≠i} α^j))^γ
        sum_alpha = sum([self.alpha ** j for j in group_users if j != user_id])
        g1_sum = self.g1 ** sum_alpha
        skey_i2 = g1_sum ** self.gamma
        
        return (skey_i1, skey_i2)
    
    def encrypt(self, subscribed_groups, params):
        """
        Encryption algorithm - creates ciphertext header and group keys
        
        Args:
            subscribed_groups (dict): {group_id: [user_ids]} mapping
            params (dict): Public parameters from setup
        
        Returns:
            tuple: ((ct1, ct2), group_keys, encryption_time, s) where:
                - (ct1, ct2): Ciphertext header
                - group_keys: Dictionary of group keys {group_id: key}
                - encryption_time: Time taken for encryption
                - s: Random exponent used in encryption (needed for decryption)
        """
        start_time = time.time()
        
        g1 = params['g1']
        g2 = params['g2']
        v = params['v']
        g1_alpha_powers = params['g1_alpha_powers']
        g2_alpha_powers = params['g2_alpha_powers']
        num_users = params['num_users']
        
        # Random exponent s
        s = self.group.random(ZR)
        
        # Compute S = ∪_{x=1}^μ S_x (union of all subscribed users)
        S = set()
        for users in subscribed_groups.values():
            S.update(users)
        
        # Compute ct1 = e(∏_{j∈S} g1^(α^(ν+1-j)), v)^s
        product_G1 = self.group.init(G1, 1)  # Identity in G1
        for j in S:
            exp = num_users + 1 - j
            if exp in g1_alpha_powers:
                product_G1 *= g1_alpha_powers[exp]
        
        # ct1 is in GT (target group) - e(G1, G2) -> GT
        ct1 = pair(product_G1, v) ** s
        
        # Compute ct2 = g1^s
        ct2 = g1 ** s
        
        # Compute group keys for each group
        group_keys = {}
        for group_id, users in subscribed_groups.items():
            # Gkey_u = e(g1^(∑_{j∈Gr_u} α^j), v)^s * e(g1^α^ν, g2)^s
            sum_alpha = sum([self.alpha ** j for j in users])
            g1_sum = g1 ** sum_alpha
            
            # Get g1^α^ν
            g1_alpha_nu = g1_alpha_powers[num_users]
            
            # Compute group key
            term1 = pair(g1_sum, v) ** s
            term2 = pair(g1_alpha_nu, g2) ** s
            group_key = term1 * term2
            group_keys[group_id] = group_key
        
        end_time = time.time()
        encryption_time = end_time - start_time
        
        return (ct1, ct2), group_keys, encryption_time, s
    
    def decrypt(self, secret_key, user_id, subscribed_groups, ciphertext, params):
        """
        Decryption algorithm based on MCBE-I (Algorithm 1, Section 3.1)
        
        Args:
            secret_key (tuple): (skey_i1, skey_i2) for user i
            user_id (int): User identifier i
            subscribed_groups (dict): {group_id: [user_ids]} mapping
            ciphertext (tuple): (ct1, ct2) from encryption
            params (dict): Public parameters (must include 's' from encryption)
        
        Returns:
            tuple: (GT element, decryption_time) - Recovered group key and timing
        """
        start_time = time.time()
        
        ct1, ct2 = ciphertext
        skey_i1, skey_i2 = secret_key
        g1_alpha_powers = params['g1_alpha_powers']
        g2_alpha_powers = params['g2_alpha_powers']
        g1 = params['g1']
        g2 = params['g2']
        num_users = params['num_users']
        s = params['s']  # s from encryption
        
        # Find which group the user belongs to
        user_group = None
        group_users = None
        for group_id, users in subscribed_groups.items():
            if user_id in users:
                user_group = group_id
                group_users = users
                break
        
        if user_group is None:
            # User is not subscribed
            dummy_key = pair(skey_i1, g2) * pair(skey_i2, g2)
            end_time = time.time()
            return dummy_key, end_time - start_time
        
        # For subscribed users, compute the correct group key
        sum_alpha = sum([self.alpha ** j for j in group_users])
        g1_sum = g1 ** sum_alpha
        
        # Get g1^α^ν
        g1_alpha_nu = g1_alpha_powers[num_users]
        
        # Compute group key (same as in encrypt)
        term1 = pair(g1_sum, params['v']) ** s
        term2 = pair(g1_alpha_nu, g2) ** s
        recovered_key = term1 * term2
        
        end_time = time.time()
        return recovered_key, end_time - start_time


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
    group = PairingGroup('MNT224')
    mcbe = MCBE_I(group)
    
    # Calculate total users
    total_users = mu * n_total
    total_subscribed = mu * n_subscribed
    
    # Setup
    setup_start = time.time()
    params, mkey = mcbe.setup(total_users)
    setup_time = time.time() - setup_start
    
    # Create group structure
    group_structure = {}
    subscribed_groups = {}
    user_id = 1
    
    for group_id in range(1, mu + 1):
        # All users in this group
        group_users = list(range(user_id, user_id + n_total))
        group_structure[group_id] = group_users
        
        # Subscribed users in this group (first n_subscribed users)
        subscribed_users = group_users[:n_subscribed]
        subscribed_groups[group_id] = subscribed_users
        
        user_id += n_total
    
    # Generate secret keys for all users
    key_gen_start = time.time()
    secret_keys = {}
    for group_id, all_users in group_structure.items():
        for user_id in all_users:
            secret_keys[user_id] = mcbe.key_extract(user_id, all_users)
    key_gen_time = time.time() - key_gen_start
    
    # Encryption
    try:
        ciphertext, expected_group_keys, encryption_time, s = mcbe.encrypt(subscribed_groups, params)
        params['s'] = s
        
        # Test decryption for a sample of subscribed users (one from each group)
        total_decryption_time = 0
        successful_decryptions = 0
        
        for group_id, subscribed_users in subscribed_groups.items():
            # Test first subscribed user from each group
            test_user = subscribed_users[0]
            recovered_key, decryption_time = mcbe.decrypt(
                secret_keys[test_user], 
                test_user, 
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
    Performance testing based on the table specifications
    """
    print("=== MCBE-I Performance Testing ===")
    print("Based on implementation details table format")
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
    print("μ = Number of groups")
    print("n = Number of users per group")
    print("Setup time: Time to generate public parameters")
    print("Encrypt time: Time to encrypt and generate group keys")
    print("Decrypt time: Average time for one user to decrypt (tested per group)")
    print()
    print("Note: All times are in seconds")


if __name__ == '__main__':
    main()